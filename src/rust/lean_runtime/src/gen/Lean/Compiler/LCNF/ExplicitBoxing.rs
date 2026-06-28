// Lean compiler output
// Module: Lean.Compiler.LCNF.ExplicitBoxing
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.AuxDeclCache Lean.Runtime
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::ExternAttr::l_Lean_isExtern;
use crate::r#gen::Lean::Compiler::LCNF::AuxDeclCache::{
    initialize_Lean_Compiler_LCNF_AuxDeclCache, l_Lean_Compiler_LCNF_cacheAuxDecl___redArg,
    runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_CtorInfo_isScalar, l_Lean_Compiler_LCNF_CtorInfo_type,
    l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit, l_Lean_Compiler_LCNF_attachCodeDecls,
    l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
    l_Lean_Compiler_LCNF_instInhabitedParam_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg,
    l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg, l_Lean_Compiler_LCNF_eraseDecl,
    l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg, l_Lean_Compiler_LCNF_findLetValue_x3f___redArg,
    l_Lean_Compiler_LCNF_getType, l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, l_Lean_Compiler_LCNF_mkLetDecl,
    l_Lean_Compiler_LCNF_mkParam, runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::ElimDead::{
    initialize_Lean_Compiler_LCNF_ElimDead, l_Lean_Compiler_LCNF_Decl_elimDeadVars,
    runtime_initialize_Lean_Compiler_LCNF_ElimDead,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, l_Lean_Compiler_LCNF_Decl_saveImpure___redArg,
    l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed,
    l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar, l_Lean_Compiler_LCNF_mkBoxedName,
    l_Lean_Expr_isVoid,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_instBEqFVarId_beq, l_Lean_instInhabitedExpr,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Runtime::{
    initialize_Lean_Runtime, l_Lean_closureMaxArgs, l_Lean_maxSmallNat,
    runtime_initialize_Lean_Runtime,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_7, lean_apply_8, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 111, 120, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 101, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1_value) as *mut LeanObject,16468567139261496664 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [114, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3_value) as *mut LeanObject,2981963283782553289 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4_value) as *mut LeanObject;
pub static l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 73, 110, 116, 56, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [95, 98, 111, 120, 101, 100, 95, 99, 111, 110, 115, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__0_value) as *mut LeanObject,318164299542928752 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 111, 98, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0_value) as *mut LeanObject,930430701391226905 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0_value) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 66, 97, 115, 105, 99, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 117, 112, 100, 97, 116, 101, 76, 101, 116, 73, 109, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 108, 105, 99, 105, 116, 66, 111, 120, 105, 110, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1_value: LeanStringObject<106> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 106, m_capacity: 106, m_length: 105, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 108, 105, 99, 105, 116, 66, 111, 120, 105, 110, 103, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 100, 101, 46, 101, 120, 112, 108, 105, 99, 105, 116, 66, 111, 120, 105, 110, 103, 46, 116, 114, 121, 67, 111, 114, 114, 101, 99, 116, 76, 101, 116, 68, 101, 99, 108, 84, 121, 112, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 103, 103, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3_value) as *mut LeanObject,13921617720798624167 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 98, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6_value) as *mut LeanObject,6552590064380865520 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 83, 105, 122, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9_value) as *mut LeanObject,17712594561405737325 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0_value: LeanStringObject<93> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 108, 105, 99, 105, 116, 66, 111, 120, 105, 110, 103, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 100, 101, 46, 101, 120, 112, 108, 105, 99, 105, 116, 66, 111, 120, 105, 110, 103, 46, 118, 105, 115, 105, 116, 76, 101, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0_value: LeanStringObject<84> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 84, m_capacity: 84, m_length: 83, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 108, 105, 99, 105, 116, 66, 111, 120, 105, 110, 103, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 100, 101, 46, 101, 120, 112, 108, 105, 99, 105, 116, 66, 111, 120, 105, 110, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_explicitBoxing___closed__0_value: LeanStringObject<15> =
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
            101, 120, 112, 108, 105, 99, 105, 116, 66, 111, 120, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_explicitBoxing___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_explicitBoxing___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_explicitBoxing___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_explicitBoxing___closed__0_value)
                as *mut LeanObject,
            2902723855926534847 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_explicitBoxing___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_explicitBoxing___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_explicitBoxing___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_explicitBoxing___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_explicitBoxing___closed__2_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_explicitBoxing___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_explicitBoxing___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_explicitBoxing___closed__2_value)
                as *mut LeanObject,
            514 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_explicitBoxing___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_explicitBoxing___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_explicitBoxing: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_explicitBoxing___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_explicitBoxing___closed__0_value) as *mut LeanObject,7338667129797042217 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [69, 120, 112, 108, 105, 99, 105, 116, 66, 111, 120, 105, 110, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,11291642946167646761 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,2225574879368775788 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,4926873135854554989 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,15721058343895336971 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,15512761812300784054 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,15744811201833996571 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,10415045817769570686 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,9318747106772198983 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,18096135551551327705 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,4315786839692695932 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,7115771451048430264 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,((( 654907530 as usize) << 1) | 1) as *mut LeanObject,7258723557332971565 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,739429607038866254 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,12179087472484021026 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,17190632358657425083 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(
    mut v_as_3030_: *mut LeanObject,
    mut v_i_3031_: usize,
    mut v_stop_3032_: usize,
) -> u8 {
    let mut v___x_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_3036_: u8 = 0;
    let mut v___x_3037_: u8 = 0;
    let mut v___y_3039_: u8 = 0;
    let mut v_type_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: usize = 0;
    let mut v___x_3043_: usize = 0;
    let mut v___x_3045_: u8 = 0;
    let mut v___x_3046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3033_ = lean_usize_dec_eq(v_i_3031_, v_stop_3032_);
                if v___x_3033_ == 0 {
                    v___x_3034_ = lean_array_uget_borrowed(v_as_3030_, v_i_3031_);
                    v_type_3035_ = lean_ctor_get(v___x_3034_, 2);
                    v_borrow_3036_ = lean_ctor_get_uint8(
                        v___x_3034_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v___x_3037_ = 1;
                    v___x_3045_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_3035_);
                    if v___x_3045_ == 0 {
                        v___y_3039_ = v_borrow_3036_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3039_ = v___x_3045_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3046_ = 0;
                    return v___x_3046_;
                }
            }
            1 => {
                if v___y_3039_ == 0 {
                    v_type_3040_ = lean_ctor_get(v___x_3034_, 2);
                    v___x_3041_ = l_Lean_Expr_isVoid(v_type_3040_);
                    if v___x_3041_ == 0 {
                        v___x_3042_ = 1usize;
                        v___x_3043_ = lean_usize_add(v_i_3031_, v___x_3042_);
                        v_i_3031_ = v___x_3043_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3037_;
                    }
                } else {
                    return v___x_3037_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0___boxed(
    mut v_as_3047_: *mut LeanObject,
    mut v_i_3048_: *mut LeanObject,
    mut v_stop_3049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3050_: usize = 0;
    let mut v_stop_boxed_3051_: usize = 0;
    let mut v_res_3052_: u8 = 0;
    let mut v_r_3053_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3050_ = lean_unbox_usize(v_i_3048_);
    lean_dec(v_i_3048_);
    v_stop_boxed_3051_ = lean_unbox_usize(v_stop_3049_);
    lean_dec(v_stop_3049_);
    v_res_3052_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_as_3047_, v_i_boxed_3050_, v_stop_boxed_3051_);
    lean_dec_ref(v_as_3047_);
    v_r_3053_ = lean_box((v_res_3052_) as usize);
    return v_r_3053_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(
    mut v_sig_3054_: *mut LeanObject,
    mut v_a_3055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3062_: u8 = 0;
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: u8 = 0;
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: u8 = 0;
    let mut v_env_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3075_: u8 = 0;
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: usize = 0;
    let mut v___x_3081_: usize = 0;
    let mut v___x_3082_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3057_ = lean_st_ref_get(v_a_3055_);
                v_name_3058_ = lean_ctor_get(v_sig_3054_, 0);
                lean_inc(v_name_3058_);
                v_type_3059_ = lean_ctor_get(v_sig_3054_, 2);
                lean_inc_ref(v_type_3059_);
                v_params_3060_ = lean_ctor_get(v_sig_3054_, 3);
                lean_inc_ref(v_params_3060_);
                lean_dec_ref(v_sig_3054_);
                v___x_3070_ = lean_unsigned_to_nat(0);
                v___x_3071_ = lean_array_get_size(v_params_3060_);
                v___x_3072_ = lean_nat_dec_lt(v___x_3070_, v___x_3071_);
                if v___x_3072_ == 0 {
                    lean_dec_ref(v_type_3059_);
                    lean_dec(v_name_3058_);
                    lean_dec(v___x_3057_);
                    v___y_3062_ = v___x_3072_;
                    state = 1;
                    continue;
                } else {
                    v_env_3073_ = lean_ctor_get(v___x_3057_, 0);
                    lean_inc_ref(v_env_3073_);
                    lean_dec(v___x_3057_);
                    v___x_3079_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_3059_);
                    lean_dec_ref(v_type_3059_);
                    if v___x_3079_ == 0 {
                        if v___x_3072_ == 0 {
                            v___y_3075_ = v___x_3079_;
                            state = 2;
                            continue;
                        } else {
                            if v___x_3072_ == 0 {
                                v___y_3075_ = v___x_3079_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3080_ = 0usize;
                                v___x_3081_ = lean_usize_of_nat(v___x_3071_);
                                v___x_3082_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_params_3060_, v___x_3080_, v___x_3081_);
                                v___y_3075_ = v___x_3082_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___y_3075_ = v___x_3079_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3062_ == 0 {
                    v___x_3063_ = l_Lean_closureMaxArgs;
                    v___x_3064_ = lean_array_get_size(v_params_3060_);
                    lean_dec_ref(v_params_3060_);
                    v___x_3065_ = lean_nat_dec_lt(v___x_3063_, v___x_3064_);
                    v___x_3066_ = lean_box((v___x_3065_) as usize);
                    v___x_3067_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3067_, 0, v___x_3066_);
                    return v___x_3067_;
                } else {
                    lean_dec_ref(v_params_3060_);
                    v___x_3068_ = lean_box((v___y_3062_) as usize);
                    v___x_3069_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3069_, 0, v___x_3068_);
                    return v___x_3069_;
                }
            }
            2 => {
                if v___y_3075_ == 0 {
                    v___x_3076_ = l_Lean_isExtern(v_env_3073_, v_name_3058_);
                    v___y_3062_ = v___x_3076_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_env_3073_);
                    lean_dec_ref(v_params_3060_);
                    lean_dec(v_name_3058_);
                    v___x_3077_ = lean_box((v___y_3075_) as usize);
                    v___x_3078_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3078_, 0, v___x_3077_);
                    return v___x_3078_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg___boxed(
    mut v_sig_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3086_: *mut LeanObject = core::ptr::null_mut();
    v_res_3086_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_sig_3083_, v_a_3084_);
    lean_dec(v_a_3084_);
    return v_res_3086_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(
    mut v_sig_3087_: *mut LeanObject,
    mut v_a_3088_: *mut LeanObject,
    mut v_a_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_sig_3087_, v_a_3091_);
    return v___x_3093_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___boxed(
    mut v_sig_3094_: *mut LeanObject,
    mut v_a_3095_: *mut LeanObject,
    mut v_a_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3100_: *mut LeanObject = core::ptr::null_mut();
    v_res_3100_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(
            v_sig_3094_,
            v_a_3095_,
            v_a_3096_,
            v_a_3097_,
            v_a_3098_,
        );
    lean_dec(v_a_3098_);
    lean_dec_ref(v_a_3097_);
    lean_dec(v_a_3096_);
    lean_dec_ref(v_a_3095_);
    return v_res_3100_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(
    mut v_sz_3101_: usize,
    mut v_i_3102_: usize,
    mut v_bs_3103_: *mut LeanObject,
    mut v___y_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u8 = 0;
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: u8 = 0;
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: usize = 0;
    let mut v___x_3122_: usize = 0;
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3109_ = lean_usize_dec_lt(v_i_3102_, v_sz_3101_);
                if v___x_3109_ == 0 {
                    v___x_3110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3110_, 0, v_bs_3103_);
                    return v___x_3110_;
                } else {
                    v_v_3111_ = lean_array_uget_borrowed(v_bs_3103_, v_i_3102_);
                    v_binderName_3112_ = lean_ctor_get(v_v_3111_, 1);
                    v_type_3113_ = lean_ctor_get(v_v_3111_, 2);
                    v___x_3114_ = 1;
                    v___x_3115_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_3113_);
                    v___x_3116_ = 0;
                    lean_inc(v_binderName_3112_);
                    v___x_3117_ = l_Lean_Compiler_LCNF_mkParam(
                        v___x_3114_,
                        v_binderName_3112_,
                        v___x_3115_,
                        v___x_3116_,
                        v___y_3104_,
                        v___y_3105_,
                        v___y_3106_,
                        v___y_3107_,
                    );
                    if lean_obj_tag(v___x_3117_) == 0 {
                        v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
                        lean_inc(v_a_3118_);
                        lean_dec_ref_known(v___x_3117_, 1);
                        v___x_3119_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3120_ = lean_array_uset(v_bs_3103_, v_i_3102_, v___x_3119_);
                        v___x_3121_ = 1usize;
                        v___x_3122_ = lean_usize_add(v_i_3102_, v___x_3121_);
                        v___x_3123_ = lean_array_uset(v_bs_x27_3120_, v_i_3102_, v_a_3118_);
                        v_i_3102_ = v___x_3122_;
                        v_bs_3103_ = v___x_3123_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_3103_);
                        v_a_3125_ = lean_ctor_get(v___x_3117_, 0);
                        v_isSharedCheck_3132_ = (!lean_is_exclusive(v___x_3117_)) as u8;
                        if v_isSharedCheck_3132_ == 0 {
                            v___x_3127_ = v___x_3117_;
                            v_isShared_3128_ = v_isSharedCheck_3132_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3125_);
                            lean_dec(v___x_3117_);
                            v___x_3127_ = lean_box(0);
                            v_isShared_3128_ = v_isSharedCheck_3132_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3128_ == 0 {
                    v___x_3130_ = v___x_3127_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0___boxed(
    mut v_sz_3133_: *mut LeanObject,
    mut v_i_3134_: *mut LeanObject,
    mut v_bs_3135_: *mut LeanObject,
    mut v___y_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
    mut v___y_3138_: *mut LeanObject,
    mut v___y_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3141_: usize = 0;
    let mut v_i_boxed_3142_: usize = 0;
    let mut v_res_3143_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3141_ = lean_unbox_usize(v_sz_3133_);
    lean_dec(v_sz_3133_);
    v_i_boxed_3142_ = lean_unbox_usize(v_i_3134_);
    lean_dec(v_i_3134_);
    v_res_3143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_boxed_3141_, v_i_boxed_3142_, v_bs_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
    lean_dec(v___y_3139_);
    lean_dec_ref(v___y_3138_);
    lean_dec(v___y_3137_);
    lean_dec_ref(v___y_3136_);
    return v_res_3143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(
    mut v_as_3145_: *mut LeanObject,
    mut v_sz_3146_: usize,
    mut v_i_3147_: usize,
    mut v_b_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: usize = 0;
    let mut v___x_3157_: usize = 0;
    let mut v___x_3159_: u8 = 0;
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v_fst_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v_array_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3184_: u8 = 0;
    let mut v_a_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: u8 = 0;
    let mut v_fvarId_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3224_: u8 = 0;
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3228_: u8 = 0;
    let mut v_reuseFailAlloc_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v_unused_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3234_: u8 = 0;
    let mut v_unused_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_unused_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3159_ = lean_usize_dec_lt(v_i_3147_, v_sz_3146_);
                if v___x_3159_ == 0 {
                    v___x_3160_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3160_, 0, v_b_3148_);
                    return v___x_3160_;
                } else {
                    v_snd_3161_ = lean_ctor_get(v_b_3148_, 1);
                    lean_inc(v_snd_3161_);
                    v_snd_3162_ = lean_ctor_get(v_snd_3161_, 1);
                    lean_inc(v_snd_3162_);
                    v_fst_3163_ = lean_ctor_get(v_b_3148_, 0);
                    v_isSharedCheck_3236_ = (!lean_is_exclusive(v_b_3148_)) as u8;
                    if v_isSharedCheck_3236_ == 0 {
                        v_unused_3237_ = lean_ctor_get(v_b_3148_, 1);
                        lean_dec(v_unused_3237_);
                        v___x_3165_ = v_b_3148_;
                        v_isShared_3166_ = v_isSharedCheck_3236_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_3163_);
                        lean_dec(v_b_3148_);
                        v___x_3165_ = lean_box(0);
                        v_isShared_3166_ = v_isSharedCheck_3236_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3156_ = 1usize;
                v___x_3157_ = lean_usize_add(v_i_3147_, v___x_3156_);
                v_i_3147_ = v___x_3157_;
                v_b_3148_ = v_a_3155_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_3167_ = lean_ctor_get(v_snd_3161_, 0);
                v_isSharedCheck_3234_ = (!lean_is_exclusive(v_snd_3161_)) as u8;
                if v_isSharedCheck_3234_ == 0 {
                    v_unused_3235_ = lean_ctor_get(v_snd_3161_, 1);
                    lean_dec(v_unused_3235_);
                    v___x_3169_ = v_snd_3161_;
                    v_isShared_3170_ = v_isSharedCheck_3234_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_3167_);
                    lean_dec(v_snd_3161_);
                    v___x_3169_ = lean_box(0);
                    v_isShared_3170_ = v_isSharedCheck_3234_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_3171_ = lean_ctor_get(v_snd_3162_, 0);
                v_start_3172_ = lean_ctor_get(v_snd_3162_, 1);
                v_stop_3173_ = lean_ctor_get(v_snd_3162_, 2);
                v___x_3174_ = lean_nat_dec_lt(v_start_3172_, v_stop_3173_);
                if v___x_3174_ == 0 {
                    if v_isShared_3170_ == 0 {
                        v___x_3176_ = v___x_3169_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_fst_3167_);
                        lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_snd_3162_);
                        v___x_3176_ = v_reuseFailAlloc_3181_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_3173_);
                    lean_inc(v_start_3172_);
                    lean_inc_ref(v_array_3171_);
                    v_isSharedCheck_3230_ = (!lean_is_exclusive(v_snd_3162_)) as u8;
                    if v_isSharedCheck_3230_ == 0 {
                        v_unused_3231_ = lean_ctor_get(v_snd_3162_, 2);
                        lean_dec(v_unused_3231_);
                        v_unused_3232_ = lean_ctor_get(v_snd_3162_, 1);
                        lean_dec(v_unused_3232_);
                        v_unused_3233_ = lean_ctor_get(v_snd_3162_, 0);
                        lean_dec(v_unused_3233_);
                        v___x_3183_ = v_snd_3162_;
                        v_isShared_3184_ = v_isSharedCheck_3230_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_snd_3162_);
                        v___x_3183_ = lean_box(0);
                        v_isShared_3184_ = v_isSharedCheck_3230_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3166_ == 0 {
                    lean_ctor_set(v___x_3165_, 1, v___x_3176_);
                    v___x_3178_ = v___x_3165_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_fst_3163_);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_3176_);
                    v___x_3178_ = v_reuseFailAlloc_3180_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3179_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3179_, 0, v___x_3178_);
                return v___x_3179_;
            }
            6 => {
                v_a_3185_ = lean_array_uget_borrowed(v_as_3145_, v_i_3147_);
                v_binderName_3186_ = lean_ctor_get(v_a_3185_, 1);
                v_type_3187_ = lean_ctor_get(v_a_3185_, 2);
                v___x_3188_ = lean_array_fget(v_array_3171_, v_start_3172_);
                v___x_3189_ = lean_unsigned_to_nat(1);
                v___x_3190_ = lean_nat_add(v_start_3172_, v___x_3189_);
                lean_dec(v_start_3172_);
                if v_isShared_3184_ == 0 {
                    lean_ctor_set(v___x_3183_, 1, v___x_3190_);
                    v___x_3192_ = v___x_3183_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_array_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3190_);
                    lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_stop_3173_);
                    v___x_3192_ = v_reuseFailAlloc_3229_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3193_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_3187_);
                if v___x_3193_ == 0 {
                    v_fvarId_3194_ = lean_ctor_get(v___x_3188_, 0);
                    lean_inc(v_fvarId_3194_);
                    lean_dec(v___x_3188_);
                    v___x_3195_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3195_, 0, v_fvarId_3194_);
                    v___x_3196_ = lean_array_push(v_fst_3167_, v___x_3195_);
                    if v_isShared_3170_ == 0 {
                        lean_ctor_set(v___x_3169_, 1, v___x_3192_);
                        lean_ctor_set(v___x_3169_, 0, v___x_3196_);
                        v___x_3198_ = v___x_3169_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3196_);
                        lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3192_);
                        v___x_3198_ = v_reuseFailAlloc_3202_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_fvarId_3203_ = lean_ctor_get(v___x_3188_, 0);
                    lean_inc(v_fvarId_3203_);
                    lean_dec(v___x_3188_);
                    v___x_3204_ = 1;
                    v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0;
                    lean_inc(v_binderName_3186_);
                    v___x_3206_ = l_Lean_Name_str___override(v_binderName_3186_, v___x_3205_);
                    v___x_3207_ = lean_alloc_ctor(14, 1, (0) as u32);
                    lean_ctor_set(v___x_3207_, 0, v_fvarId_3203_);
                    lean_inc_ref(v_type_3187_);
                    v___x_3208_ = l_Lean_Compiler_LCNF_mkLetDecl(
                        v___x_3204_,
                        v___x_3206_,
                        v_type_3187_,
                        v___x_3207_,
                        v___y_3149_,
                        v___y_3150_,
                        v___y_3151_,
                        v___y_3152_,
                    );
                    if lean_obj_tag(v___x_3208_) == 0 {
                        v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
                        lean_inc(v_a_3209_);
                        lean_dec_ref_known(v___x_3208_, 1);
                        v_fvarId_3210_ = lean_ctor_get(v_a_3209_, 0);
                        lean_inc(v_fvarId_3210_);
                        v___x_3211_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3211_, 0, v_a_3209_);
                        v___x_3212_ = lean_array_push(v_fst_3163_, v___x_3211_);
                        v___x_3213_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3213_, 0, v_fvarId_3210_);
                        v___x_3214_ = lean_array_push(v_fst_3167_, v___x_3213_);
                        if v_isShared_3170_ == 0 {
                            lean_ctor_set(v___x_3169_, 1, v___x_3192_);
                            lean_ctor_set(v___x_3169_, 0, v___x_3214_);
                            v___x_3216_ = v___x_3169_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3214_);
                            lean_ctor_set(v_reuseFailAlloc_3220_, 1, v___x_3192_);
                            v___x_3216_ = v_reuseFailAlloc_3220_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3192_);
                        lean_del_object(v___x_3169_);
                        lean_dec(v_fst_3167_);
                        lean_del_object(v___x_3165_);
                        lean_dec(v_fst_3163_);
                        v_a_3221_ = lean_ctor_get(v___x_3208_, 0);
                        v_isSharedCheck_3228_ = (!lean_is_exclusive(v___x_3208_)) as u8;
                        if v_isSharedCheck_3228_ == 0 {
                            v___x_3223_ = v___x_3208_;
                            v_isShared_3224_ = v_isSharedCheck_3228_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_3221_);
                            lean_dec(v___x_3208_);
                            v___x_3223_ = lean_box(0);
                            v_isShared_3224_ = v_isSharedCheck_3228_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_isShared_3166_ == 0 {
                    lean_ctor_set(v___x_3165_, 1, v___x_3198_);
                    v___x_3200_ = v___x_3165_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_fst_3163_);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3198_);
                    v___x_3200_ = v_reuseFailAlloc_3201_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_3155_ = v___x_3200_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_3166_ == 0 {
                    lean_ctor_set(v___x_3165_, 1, v___x_3216_);
                    lean_ctor_set(v___x_3165_, 0, v___x_3212_);
                    v___x_3218_ = v___x_3165_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3212_);
                    lean_ctor_set(v_reuseFailAlloc_3219_, 1, v___x_3216_);
                    v___x_3218_ = v_reuseFailAlloc_3219_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_3155_ = v___x_3218_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_3224_ == 0 {
                    v___x_3226_ = v___x_3223_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
                    v___x_3226_ = v_reuseFailAlloc_3227_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___boxed(
    mut v_as_3238_: *mut LeanObject,
    mut v_sz_3239_: *mut LeanObject,
    mut v_i_3240_: *mut LeanObject,
    mut v_b_3241_: *mut LeanObject,
    mut v___y_3242_: *mut LeanObject,
    mut v___y_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3247_: usize = 0;
    let mut v_i_boxed_3248_: usize = 0;
    let mut v_res_3249_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3247_ = lean_unbox_usize(v_sz_3239_);
    lean_dec(v_sz_3239_);
    v_i_boxed_3248_ = lean_unbox_usize(v_i_3240_);
    lean_dec(v_i_3240_);
    v_res_3249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_as_3238_, v_sz_boxed_3247_, v_i_boxed_3248_, v_b_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
    lean_dec(v___y_3245_);
    lean_dec_ref(v___y_3244_);
    lean_dec(v___y_3243_);
    lean_dec_ref(v___y_3242_);
    lean_dec_ref(v_as_3238_);
    return v_res_3249_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(
    mut v_sig_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
    mut v_a_3262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v_sz_3270_: usize = 0;
    let mut v___x_3271_: usize = 0;
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: u8 = 0;
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut v_unused_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3303_: u8 = 0;
    let mut v_reuseFailAlloc_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3319_: u8 = 0;
    let mut v_fst_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: u8 = 0;
    let mut v_fvarId_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v_reuseFailAlloc_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3360_: u8 = 0;
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_reuseFailAlloc_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3366_: u8 = 0;
    let mut v_unused_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_a_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3376_: u8 = 0;
    let mut v_a_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_isSharedCheck_3385_: u8 = 0;
    let mut v_unused_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3264_ = lean_ctor_get(v_sig_3258_, 0);
                v_type_3265_ = lean_ctor_get(v_sig_3258_, 2);
                v_params_3266_ = lean_ctor_get(v_sig_3258_, 3);
                v_isSharedCheck_3385_ = (!lean_is_exclusive(v_sig_3258_)) as u8;
                if v_isSharedCheck_3385_ == 0 {
                    v_unused_3386_ = lean_ctor_get(v_sig_3258_, 1);
                    lean_dec(v_unused_3386_);
                    v___x_3268_ = v_sig_3258_;
                    v_isShared_3269_ = v_isSharedCheck_3385_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_params_3266_);
                    lean_inc(v_type_3265_);
                    lean_inc(v_name_3264_);
                    lean_dec(v_sig_3258_);
                    v___x_3268_ = lean_box(0);
                    v_isShared_3269_ = v_isSharedCheck_3385_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_3270_ = lean_array_size(v_params_3266_);
                v___x_3271_ = 0usize;
                lean_inc_ref(v_params_3266_);
                v___x_3272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_3270_, v___x_3271_, v_params_3266_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
                if lean_obj_tag(v___x_3272_) == 0 {
                    v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
                    lean_inc_n(v_a_3273_, 2);
                    lean_dec_ref_known(v___x_3272_, 1);
                    v___x_3305_ = lean_unsigned_to_nat(0);
                    v___x_3306_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0;
                    v___x_3307_ = lean_array_get_size(v_params_3266_);
                    v___x_3308_ = lean_mk_empty_array_with_capacity(v___x_3307_);
                    v___x_3309_ = lean_array_get_size(v_a_3273_);
                    v___x_3310_ = l_Array_toSubarray___redArg(v_a_3273_, v___x_3305_, v___x_3309_);
                    v___x_3311_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3311_, 0, v___x_3308_);
                    lean_ctor_set(v___x_3311_, 1, v___x_3310_);
                    v___x_3312_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3312_, 0, v___x_3306_);
                    lean_ctor_set(v___x_3312_, 1, v___x_3311_);
                    v___x_3313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_params_3266_, v_sz_3270_, v___x_3271_, v___x_3312_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
                    lean_dec_ref(v_params_3266_);
                    if lean_obj_tag(v___x_3313_) == 0 {
                        v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
                        lean_inc(v_a_3314_);
                        lean_dec_ref_known(v___x_3313_, 1);
                        v_snd_3315_ = lean_ctor_get(v_a_3314_, 1);
                        v_fst_3316_ = lean_ctor_get(v_a_3314_, 0);
                        v_isSharedCheck_3368_ = (!lean_is_exclusive(v_a_3314_)) as u8;
                        if v_isSharedCheck_3368_ == 0 {
                            v___x_3318_ = v_a_3314_;
                            v_isShared_3319_ = v_isSharedCheck_3368_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_snd_3315_);
                            lean_inc(v_fst_3316_);
                            lean_dec(v_a_3314_);
                            v___x_3318_ = lean_box(0);
                            v_isShared_3319_ = v_isSharedCheck_3368_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3273_);
                        lean_del_object(v___x_3268_);
                        lean_dec_ref(v_type_3265_);
                        lean_dec(v_name_3264_);
                        v_a_3369_ = lean_ctor_get(v___x_3313_, 0);
                        v_isSharedCheck_3376_ = (!lean_is_exclusive(v___x_3313_)) as u8;
                        if v_isSharedCheck_3376_ == 0 {
                            v___x_3371_ = v___x_3313_;
                            v_isShared_3372_ = v_isSharedCheck_3376_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_3369_);
                            lean_dec(v___x_3313_);
                            v___x_3371_ = lean_box(0);
                            v_isShared_3372_ = v_isSharedCheck_3376_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3268_);
                    lean_dec_ref(v_params_3266_);
                    lean_dec_ref(v_type_3265_);
                    lean_dec(v_name_3264_);
                    v_a_3377_ = lean_ctor_get(v___x_3272_, 0);
                    v_isSharedCheck_3384_ = (!lean_is_exclusive(v___x_3272_)) as u8;
                    if v_isSharedCheck_3384_ == 0 {
                        v___x_3379_ = v___x_3272_;
                        v_isShared_3380_ = v_isSharedCheck_3384_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_3377_);
                        lean_dec(v___x_3272_);
                        v___x_3379_ = lean_box(0);
                        v_isShared_3380_ = v_isSharedCheck_3384_;
                        state = 18;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3277_ = l_Lean_Compiler_LCNF_mkBoxedName(v_name_3264_);
                v___x_3278_ = lean_box(0);
                v___x_3279_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_3265_);
                lean_dec_ref(v_type_3265_);
                v___x_3280_ = 1;
                if v_isShared_3269_ == 0 {
                    lean_ctor_set(v___x_3268_, 3, v_a_3273_);
                    lean_ctor_set(v___x_3268_, 2, v___x_3279_);
                    lean_ctor_set(v___x_3268_, 1, v___x_3278_);
                    lean_ctor_set(v___x_3268_, 0, v___x_3277_);
                    v___x_3282_ = v___x_3268_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3277_);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 1, v___x_3278_);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 2, v___x_3279_);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_a_3273_);
                    v___x_3282_ = v_reuseFailAlloc_3304_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_3282_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___x_3280_,
                );
                v___x_3283_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3283_, 0, v_value_3275_);
                v___x_3284_ = 0;
                v___x_3285_ = lean_box(0);
                v___x_3286_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3286_, 0, v___x_3282_);
                lean_ctor_set(v___x_3286_, 1, v___x_3283_);
                lean_ctor_set(v___x_3286_, 2, v___x_3285_);
                lean_ctor_set_uint8(
                    v___x_3286_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3284_,
                );
                lean_inc_ref(v___x_3286_);
                v___x_3287_ =
                    l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_3286_, v___y_3276_);
                if lean_obj_tag(v___x_3287_) == 0 {
                    v_isSharedCheck_3294_ = (!lean_is_exclusive(v___x_3287_)) as u8;
                    if v_isSharedCheck_3294_ == 0 {
                        v_unused_3295_ = lean_ctor_get(v___x_3287_, 0);
                        lean_dec(v_unused_3295_);
                        v___x_3289_ = v___x_3287_;
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_3287_);
                        v___x_3289_ = lean_box(0);
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_3286_, 3);
                    v_a_3296_ = lean_ctor_get(v___x_3287_, 0);
                    v_isSharedCheck_3303_ = (!lean_is_exclusive(v___x_3287_)) as u8;
                    if v_isSharedCheck_3303_ == 0 {
                        v___x_3298_ = v___x_3287_;
                        v_isShared_3299_ = v_isSharedCheck_3303_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3296_);
                        lean_dec(v___x_3287_);
                        v___x_3298_ = lean_box(0);
                        v_isShared_3299_ = v_isSharedCheck_3303_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3290_ == 0 {
                    lean_ctor_set(v___x_3289_, 0, v___x_3286_);
                    v___x_3292_ = v___x_3289_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3286_);
                    v___x_3292_ = v_reuseFailAlloc_3293_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3292_;
            }
            6 => {
                if v_isShared_3299_ == 0 {
                    v___x_3301_ = v___x_3298_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
                    v___x_3301_ = v_reuseFailAlloc_3302_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3301_;
            }
            8 => {
                v_fst_3320_ = lean_ctor_get(v_snd_3315_, 0);
                v_isSharedCheck_3366_ = (!lean_is_exclusive(v_snd_3315_)) as u8;
                if v_isSharedCheck_3366_ == 0 {
                    v_unused_3367_ = lean_ctor_get(v_snd_3315_, 1);
                    lean_dec(v_unused_3367_);
                    v___x_3322_ = v_snd_3315_;
                    v_isShared_3323_ = v_isSharedCheck_3366_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_fst_3320_);
                    lean_dec(v_snd_3315_);
                    v___x_3322_ = lean_box(0);
                    v_isShared_3323_ = v_isSharedCheck_3366_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3324_ = 1;
                v___x_3325_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2;
                lean_inc(v_name_3264_);
                if v_isShared_3323_ == 0 {
                    lean_ctor_set_tag(v___x_3322_, 9);
                    lean_ctor_set(v___x_3322_, 1, v_fst_3320_);
                    lean_ctor_set(v___x_3322_, 0, v_name_3264_);
                    v___x_3327_ = v___x_3322_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3365_ = lean_alloc_ctor(9, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_name_3264_);
                    lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_fst_3320_);
                    v___x_3327_ = v_reuseFailAlloc_3365_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                lean_inc_ref(v_type_3265_);
                v___x_3328_ = l_Lean_Compiler_LCNF_mkLetDecl(
                    v___x_3324_,
                    v___x_3325_,
                    v_type_3265_,
                    v___x_3327_,
                    v_a_3259_,
                    v_a_3260_,
                    v_a_3261_,
                    v_a_3262_,
                );
                if lean_obj_tag(v___x_3328_) == 0 {
                    v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
                    lean_inc_n(v_a_3329_, 2);
                    lean_dec_ref_known(v___x_3328_, 1);
                    v___x_3330_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3330_, 0, v_a_3329_);
                    v___x_3331_ = lean_array_push(v_fst_3316_, v___x_3330_);
                    v___x_3332_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_3265_);
                    if v___x_3332_ == 0 {
                        lean_del_object(v___x_3318_);
                        v_fvarId_3333_ = lean_ctor_get(v_a_3329_, 0);
                        lean_inc(v_fvarId_3333_);
                        lean_dec(v_a_3329_);
                        v___x_3334_ = lean_alloc_ctor(5, 1, (0) as u32);
                        lean_ctor_set(v___x_3334_, 0, v_fvarId_3333_);
                        v___x_3335_ = l_Lean_Compiler_LCNF_attachCodeDecls(
                            v___x_3324_,
                            v___x_3331_,
                            v___x_3334_,
                        );
                        lean_dec_ref(v___x_3331_);
                        v_value_3275_ = v___x_3335_;
                        v___y_3276_ = v_a_3262_;
                        state = 2;
                        continue;
                    } else {
                        v_fvarId_3336_ = lean_ctor_get(v_a_3329_, 0);
                        lean_inc(v_fvarId_3336_);
                        lean_dec(v_a_3329_);
                        v___x_3337_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4;
                        v___x_3338_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_3265_);
                        lean_inc_ref(v_type_3265_);
                        if v_isShared_3319_ == 0 {
                            lean_ctor_set_tag(v___x_3318_, 13);
                            lean_ctor_set(v___x_3318_, 1, v_fvarId_3336_);
                            lean_ctor_set(v___x_3318_, 0, v_type_3265_);
                            v___x_3340_ = v___x_3318_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3356_ = lean_alloc_ctor(13, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_type_3265_);
                            lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_fvarId_3336_);
                            v___x_3340_ = v_reuseFailAlloc_3356_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3318_);
                    lean_dec(v_fst_3316_);
                    lean_dec(v_a_3273_);
                    lean_del_object(v___x_3268_);
                    lean_dec_ref(v_type_3265_);
                    lean_dec(v_name_3264_);
                    v_a_3357_ = lean_ctor_get(v___x_3328_, 0);
                    v_isSharedCheck_3364_ = (!lean_is_exclusive(v___x_3328_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v___x_3359_ = v___x_3328_;
                        v_isShared_3360_ = v_isSharedCheck_3364_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_3357_);
                        lean_dec(v___x_3328_);
                        v___x_3359_ = lean_box(0);
                        v_isShared_3360_ = v_isSharedCheck_3364_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v___x_3341_ = l_Lean_Compiler_LCNF_mkLetDecl(
                    v___x_3324_,
                    v___x_3337_,
                    v___x_3338_,
                    v___x_3340_,
                    v_a_3259_,
                    v_a_3260_,
                    v_a_3261_,
                    v_a_3262_,
                );
                if lean_obj_tag(v___x_3341_) == 0 {
                    v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
                    lean_inc(v_a_3342_);
                    lean_dec_ref_known(v___x_3341_, 1);
                    v_fvarId_3343_ = lean_ctor_get(v_a_3342_, 0);
                    lean_inc(v_fvarId_3343_);
                    v___x_3344_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3344_, 0, v_a_3342_);
                    v___x_3345_ = lean_array_push(v___x_3331_, v___x_3344_);
                    v___x_3346_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v___x_3346_, 0, v_fvarId_3343_);
                    v___x_3347_ =
                        l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3324_, v___x_3345_, v___x_3346_);
                    lean_dec_ref(v___x_3345_);
                    v_value_3275_ = v___x_3347_;
                    v___y_3276_ = v_a_3262_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v___x_3331_);
                    lean_dec(v_a_3273_);
                    lean_del_object(v___x_3268_);
                    lean_dec_ref(v_type_3265_);
                    lean_dec(v_name_3264_);
                    v_a_3348_ = lean_ctor_get(v___x_3341_, 0);
                    v_isSharedCheck_3355_ = (!lean_is_exclusive(v___x_3341_)) as u8;
                    if v_isSharedCheck_3355_ == 0 {
                        v___x_3350_ = v___x_3341_;
                        v_isShared_3351_ = v_isSharedCheck_3355_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3348_);
                        lean_dec(v___x_3341_);
                        v___x_3350_ = lean_box(0);
                        v_isShared_3351_ = v_isSharedCheck_3355_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_3351_ == 0 {
                    v___x_3353_ = v___x_3350_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
                    v___x_3353_ = v_reuseFailAlloc_3354_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3353_;
            }
            14 => {
                if v_isShared_3360_ == 0 {
                    v___x_3362_ = v___x_3359_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
                    v___x_3362_ = v_reuseFailAlloc_3363_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3362_;
            }
            16 => {
                if v_isShared_3372_ == 0 {
                    v___x_3374_ = v___x_3371_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
                    v___x_3374_ = v_reuseFailAlloc_3375_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3374_;
            }
            18 => {
                if v_isShared_3380_ == 0 {
                    v___x_3382_ = v___x_3379_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___boxed(
    mut v_sig_3387_: *mut LeanObject,
    mut v_a_3388_: *mut LeanObject,
    mut v_a_3389_: *mut LeanObject,
    mut v_a_3390_: *mut LeanObject,
    mut v_a_3391_: *mut LeanObject,
    mut v_a_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3393_: *mut LeanObject = core::ptr::null_mut();
    v_res_3393_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(
            v_sig_3387_,
            v_a_3388_,
            v_a_3389_,
            v_a_3390_,
            v_a_3391_,
        );
    lean_dec(v_a_3391_);
    lean_dec_ref(v_a_3390_);
    lean_dec(v_a_3389_);
    lean_dec_ref(v_a_3388_);
    return v_res_3393_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(
    mut v_as_3394_: *mut LeanObject,
    mut v_i_3395_: usize,
    mut v_stop_3396_: usize,
    mut v_b_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: usize = 0;
    let mut v___x_3406_: usize = 0;
    let mut v___x_3408_: u8 = 0;
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: u8 = 0;
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3420_: u8 = 0;
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3424_: u8 = 0;
    let mut v_a_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3428_: u8 = 0;
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3408_ = lean_usize_dec_eq(v_i_3395_, v_stop_3396_);
                if v___x_3408_ == 0 {
                    v___x_3409_ = lean_array_uget_borrowed(v_as_3394_, v_i_3395_);
                    v_toSignature_3410_ = lean_ctor_get(v___x_3409_, 0);
                    lean_inc_ref(v_toSignature_3410_);
                    v___x_3411_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_toSignature_3410_, v___y_3401_);
                    if lean_obj_tag(v___x_3411_) == 0 {
                        v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
                        lean_inc(v_a_3412_);
                        lean_dec_ref_known(v___x_3411_, 1);
                        v___x_3413_ = (lean_unbox(v_a_3412_) as u8);
                        lean_dec(v_a_3412_);
                        if v___x_3413_ == 0 {
                            v_a_3404_ = v_b_3397_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc_ref(v_toSignature_3410_);
                            v___x_3414_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_toSignature_3410_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
                            if lean_obj_tag(v___x_3414_) == 0 {
                                v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
                                lean_inc(v_a_3415_);
                                lean_dec_ref_known(v___x_3414_, 1);
                                v___x_3416_ = lean_array_push(v_b_3397_, v_a_3415_);
                                v_a_3404_ = v___x_3416_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_b_3397_);
                                v_a_3417_ = lean_ctor_get(v___x_3414_, 0);
                                v_isSharedCheck_3424_ = (!lean_is_exclusive(v___x_3414_)) as u8;
                                if v_isSharedCheck_3424_ == 0 {
                                    v___x_3419_ = v___x_3414_;
                                    v_isShared_3420_ = v_isSharedCheck_3424_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_3417_);
                                    lean_dec(v___x_3414_);
                                    v___x_3419_ = lean_box(0);
                                    v_isShared_3420_ = v_isSharedCheck_3424_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_3397_);
                        v_a_3425_ = lean_ctor_get(v___x_3411_, 0);
                        v_isSharedCheck_3432_ = (!lean_is_exclusive(v___x_3411_)) as u8;
                        if v_isSharedCheck_3432_ == 0 {
                            v___x_3427_ = v___x_3411_;
                            v_isShared_3428_ = v_isSharedCheck_3432_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3425_);
                            lean_dec(v___x_3411_);
                            v___x_3427_ = lean_box(0);
                            v_isShared_3428_ = v_isSharedCheck_3432_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_3433_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3433_, 0, v_b_3397_);
                    return v___x_3433_;
                }
            }
            1 => {
                v___x_3405_ = 1usize;
                v___x_3406_ = lean_usize_add(v_i_3395_, v___x_3405_);
                v_i_3395_ = v___x_3406_;
                v_b_3397_ = v_a_3404_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3420_ == 0 {
                    v___x_3422_ = v___x_3419_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
                    v___x_3422_ = v_reuseFailAlloc_3423_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3422_;
            }
            4 => {
                if v_isShared_3428_ == 0 {
                    v___x_3430_ = v___x_3427_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
                    v___x_3430_ = v_reuseFailAlloc_3431_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0___boxed(
    mut v_as_3434_: *mut LeanObject,
    mut v_i_3435_: *mut LeanObject,
    mut v_stop_3436_: *mut LeanObject,
    mut v_b_3437_: *mut LeanObject,
    mut v___y_3438_: *mut LeanObject,
    mut v___y_3439_: *mut LeanObject,
    mut v___y_3440_: *mut LeanObject,
    mut v___y_3441_: *mut LeanObject,
    mut v___y_3442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3443_: usize = 0;
    let mut v_stop_boxed_3444_: usize = 0;
    let mut v_res_3445_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3443_ = lean_unbox_usize(v_i_3435_);
    lean_dec(v_i_3435_);
    v_stop_boxed_3444_ = lean_unbox_usize(v_stop_3436_);
    lean_dec(v_stop_3436_);
    v_res_3445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_3434_, v_i_boxed_3443_, v_stop_boxed_3444_, v_b_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
    lean_dec(v___y_3441_);
    lean_dec_ref(v___y_3440_);
    lean_dec(v___y_3439_);
    lean_dec_ref(v___y_3438_);
    lean_dec_ref(v_as_3434_);
    return v_res_3445_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(
    mut v_as_3448_: *mut LeanObject,
    mut v_start_3449_: *mut LeanObject,
    mut v_stop_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
    mut v___y_3452_: *mut LeanObject,
    mut v___y_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: u8 = 0;
    v___x_3456_ =
        l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0;
    v___x_3457_ = lean_nat_dec_lt(v_start_3449_, v_stop_3450_);
    if v___x_3457_ == 0 {
        let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
        v___x_3458_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3458_, 0, v___x_3456_);
        return v___x_3458_;
    } else {
        let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3460_: u8 = 0;
        v___x_3459_ = lean_array_get_size(v_as_3448_);
        v___x_3460_ = lean_nat_dec_le(v_stop_3450_, v___x_3459_);
        if v___x_3460_ == 0 {
            let mut v___x_3461_: u8 = 0;
            v___x_3461_ = lean_nat_dec_lt(v_start_3449_, v___x_3459_);
            if v___x_3461_ == 0 {
                let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
                v___x_3462_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3462_, 0, v___x_3456_);
                return v___x_3462_;
            } else {
                let mut v___x_3463_: usize = 0;
                let mut v___x_3464_: usize = 0;
                let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
                v___x_3463_ = lean_usize_of_nat(v_start_3449_);
                v___x_3464_ = lean_usize_of_nat(v___x_3459_);
                v___x_3465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_3448_, v___x_3463_, v___x_3464_, v___x_3456_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
                return v___x_3465_;
            }
        } else {
            let mut v___x_3466_: usize = 0;
            let mut v___x_3467_: usize = 0;
            let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
            v___x_3466_ = lean_usize_of_nat(v_start_3449_);
            v___x_3467_ = lean_usize_of_nat(v_stop_3450_);
            v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_3448_, v___x_3466_, v___x_3467_, v___x_3456_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
            return v___x_3468_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___boxed(
    mut v_as_3469_: *mut LeanObject,
    mut v_start_3470_: *mut LeanObject,
    mut v_stop_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
    mut v___y_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3477_: *mut LeanObject = core::ptr::null_mut();
    v_res_3477_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(
        v_as_3469_,
        v_start_3470_,
        v_stop_3471_,
        v___y_3472_,
        v___y_3473_,
        v___y_3474_,
        v___y_3475_,
    );
    lean_dec(v___y_3475_);
    lean_dec_ref(v___y_3474_);
    lean_dec(v___y_3473_);
    lean_dec_ref(v___y_3472_);
    lean_dec(v_stop_3471_);
    lean_dec(v_start_3470_);
    lean_dec_ref(v_as_3469_);
    return v_res_3477_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addBoxedVersions(
    mut v_decls_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
    mut v_a_3480_: *mut LeanObject,
    mut v_a_3481_: *mut LeanObject,
    mut v_a_3482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3484_ = lean_unsigned_to_nat(0);
                v___x_3485_ = lean_array_get_size(v_decls_3478_);
                v___x_3486_ =
                    l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(
                        v_decls_3478_,
                        v___x_3484_,
                        v___x_3485_,
                        v_a_3479_,
                        v_a_3480_,
                        v_a_3481_,
                        v_a_3482_,
                    );
                if lean_obj_tag(v___x_3486_) == 0 {
                    v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
                    v_isSharedCheck_3495_ = (!lean_is_exclusive(v___x_3486_)) as u8;
                    if v_isSharedCheck_3495_ == 0 {
                        v___x_3489_ = v___x_3486_;
                        v_isShared_3490_ = v_isSharedCheck_3495_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3487_);
                        lean_dec(v___x_3486_);
                        v___x_3489_ = lean_box(0);
                        v_isShared_3490_ = v_isSharedCheck_3495_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decls_3478_);
                    return v___x_3486_;
                }
            }
            1 => {
                v___x_3491_ = l_Array_append___redArg(v_decls_3478_, v_a_3487_);
                lean_dec(v_a_3487_);
                if v_isShared_3490_ == 0 {
                    lean_ctor_set(v___x_3489_, 0, v___x_3491_);
                    v___x_3493_ = v___x_3489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
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
pub unsafe fn l_Lean_Compiler_LCNF_addBoxedVersions___boxed(
    mut v_decls_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
    mut v_a_3501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3502_: *mut LeanObject = core::ptr::null_mut();
    v_res_3502_ = l_Lean_Compiler_LCNF_addBoxedVersions(
        v_decls_3496_,
        v_a_3497_,
        v_a_3498_,
        v_a_3499_,
        v_a_3500_,
    );
    lean_dec(v_a_3500_);
    lean_dec_ref(v_a_3499_);
    lean_dec(v_a_3498_);
    lean_dec_ref(v_a_3497_);
    return v_res_3502_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(
    mut v_a_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currDeclResultType_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    v_currDeclResultType_3505_ = lean_ctor_get(v_a_3503_, 1);
    lean_inc_ref(v_currDeclResultType_3505_);
    v___x_3506_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3506_, 0, v_currDeclResultType_3505_);
    return v___x_3506_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg___boxed(
    mut v_a_3507_: *mut LeanObject,
    mut v_a_3508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3509_: *mut LeanObject = core::ptr::null_mut();
    v_res_3509_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(
            v_a_3507_,
        );
    lean_dec_ref(v_a_3507_);
    return v_res_3509_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(
    mut v_a_3510_: *mut LeanObject,
    mut v_a_3511_: *mut LeanObject,
    mut v_a_3512_: *mut LeanObject,
    mut v_a_3513_: *mut LeanObject,
    mut v_a_3514_: *mut LeanObject,
    mut v_a_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currDeclResultType_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    v_currDeclResultType_3517_ = lean_ctor_get(v_a_3510_, 1);
    lean_inc_ref(v_currDeclResultType_3517_);
    v___x_3518_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3518_, 0, v_currDeclResultType_3517_);
    return v___x_3518_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___boxed(
    mut v_a_3519_: *mut LeanObject,
    mut v_a_3520_: *mut LeanObject,
    mut v_a_3521_: *mut LeanObject,
    mut v_a_3522_: *mut LeanObject,
    mut v_a_3523_: *mut LeanObject,
    mut v_a_3524_: *mut LeanObject,
    mut v_a_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3526_: *mut LeanObject = core::ptr::null_mut();
    v_res_3526_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(
        v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_,
    );
    lean_dec(v_a_3524_);
    lean_dec_ref(v_a_3523_);
    lean_dec(v_a_3522_);
    lean_dec_ref(v_a_3521_);
    lean_dec(v_a_3520_);
    lean_dec_ref(v_a_3519_);
    return v_res_3526_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(
    mut v_t_u2081_3527_: *mut LeanObject,
    mut v_t_u2082_3528_: *mut LeanObject,
) -> u8 {
    let mut v___y_3530_: u8 = 0;
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: u8 = 0;
    let mut v___y_3534_: u8 = 0;
    let mut v___x_3535_: u8 = 0;
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3535_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_3527_);
                v___x_3536_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2082_3528_);
                if v___x_3535_ == 0 {
                    if v___x_3536_ == 0 {
                        v___x_3537_ = 1;
                        v___y_3530_ = v___x_3537_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3534_ = v___x_3535_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_3534_ = v___x_3536_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3531_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_3527_);
                if v___x_3531_ == 0 {
                    return v___y_3530_;
                } else {
                    v___x_3532_ = lean_expr_eqv(v_t_u2081_3527_, v_t_u2082_3528_);
                    return v___x_3532_;
                }
            }
            2 => {
                if v___y_3534_ == 0 {
                    return v___y_3534_;
                } else {
                    v___y_3530_ = v___y_3534_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing___boxed(
    mut v_t_u2081_3538_: *mut LeanObject,
    mut v_t_u2082_3539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3540_: u8 = 0;
    let mut v_r_3541_: *mut LeanObject = core::ptr::null_mut();
    v_res_3540_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(
            v_t_u2081_3538_,
            v_t_u2082_3539_,
        );
    lean_dec_ref(v_t_u2082_3539_);
    lean_dec_ref(v_t_u2081_3538_);
    v_r_3541_ = lean_box((v_res_3540_) as usize);
    return v_r_3541_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(
    mut v_x_3544_: *mut LeanObject,
    mut v_xType_3545_: *mut LeanObject,
    mut v_a_3546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: u8 = 0;
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: u8 = 0;
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3560_: u8 = 0;
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3565_: u8 = 0;
    let mut v_unused_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3574_: u8 = 0;
    let mut v_unused_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3583_: u8 = 0;
    let mut v_unused_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: u8 = 0;
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_xType_3545_) == 4 {
                    v_declName_3588_ = lean_ctor_get(v_xType_3545_, 0);
                    if lean_obj_tag(v_declName_3588_) == 1 {
                        v_pre_3589_ = lean_ctor_get(v_declName_3588_, 0);
                        if lean_obj_tag(v_pre_3589_) == 0 {
                            v_us_3590_ = lean_ctor_get(v_xType_3545_, 1);
                            v_str_3591_ = lean_ctor_get(v_declName_3588_, 1);
                            v___x_3592_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0;
                            v___x_3593_ = lean_string_dec_eq(v_str_3591_, v___x_3592_);
                            if v___x_3593_ == 0 {
                                v___x_3594_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1;
                                v___x_3595_ = lean_string_dec_eq(v_str_3591_, v___x_3594_);
                                if v___x_3595_ == 0 {
                                    v___y_3549_ = v_a_3546_;
                                    state = 1;
                                    continue;
                                } else {
                                    if lean_obj_tag(v_us_3590_) == 0 {
                                        state = 8;
                                        continue;
                                    } else {
                                        v___y_3549_ = v_a_3546_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                if lean_obj_tag(v_us_3590_) == 0 {
                                    state = 8;
                                    continue;
                                } else {
                                    v___y_3549_ = v_a_3546_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___y_3549_ = v_a_3546_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_3549_ = v_a_3546_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_3549_ = v_a_3546_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3550_ = 1;
                v___x_3551_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                    v___x_3550_,
                    v_x_3544_,
                    v___y_3549_,
                );
                if lean_obj_tag(v___x_3551_) == 0 {
                    v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
                    lean_inc(v_a_3552_);
                    if lean_obj_tag(v_a_3552_) == 1 {
                        v_val_3553_ = lean_ctor_get(v_a_3552_, 0);
                        lean_inc(v_val_3553_);
                        lean_dec_ref_known(v_a_3552_, 1);
                        match lean_obj_tag(v_val_3553_) {
                            0 => {
                                lean_dec_ref_known(v_val_3553_, 1);
                                return v___x_3551_;
                            }
                            9 => {
                                v_args_3554_ = lean_ctor_get(v_val_3553_, 1);
                                lean_inc_ref(v_args_3554_);
                                lean_dec_ref_known(v_val_3553_, 2);
                                v___x_3555_ = lean_array_get_size(v_args_3554_);
                                lean_dec_ref(v_args_3554_);
                                v___x_3556_ = lean_unsigned_to_nat(0);
                                v___x_3557_ = lean_nat_dec_eq(v___x_3555_, v___x_3556_);
                                if v___x_3557_ == 0 {
                                    v_isSharedCheck_3565_ = (!lean_is_exclusive(v___x_3551_)) as u8;
                                    if v_isSharedCheck_3565_ == 0 {
                                        v_unused_3566_ = lean_ctor_get(v___x_3551_, 0);
                                        lean_dec(v_unused_3566_);
                                        v___x_3559_ = v___x_3551_;
                                        v_isShared_3560_ = v_isSharedCheck_3565_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3551_);
                                        v___x_3559_ = lean_box(0);
                                        v_isShared_3560_ = v_isSharedCheck_3565_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    return v___x_3551_;
                                }
                            }
                            _ => {
                                lean_dec(v_val_3553_);
                                v_isSharedCheck_3574_ = (!lean_is_exclusive(v___x_3551_)) as u8;
                                if v_isSharedCheck_3574_ == 0 {
                                    v_unused_3575_ = lean_ctor_get(v___x_3551_, 0);
                                    lean_dec(v_unused_3575_);
                                    v___x_3568_ = v___x_3551_;
                                    v_isShared_3569_ = v_isSharedCheck_3574_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_dec(v___x_3551_);
                                    v___x_3568_ = lean_box(0);
                                    v_isShared_3569_ = v_isSharedCheck_3574_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_3552_);
                        v_isSharedCheck_3583_ = (!lean_is_exclusive(v___x_3551_)) as u8;
                        if v_isSharedCheck_3583_ == 0 {
                            v_unused_3584_ = lean_ctor_get(v___x_3551_, 0);
                            lean_dec(v_unused_3584_);
                            v___x_3577_ = v___x_3551_;
                            v_isShared_3578_ = v_isSharedCheck_3583_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v___x_3551_);
                            v___x_3577_ = lean_box(0);
                            v_isShared_3578_ = v_isSharedCheck_3583_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    return v___x_3551_;
                }
            }
            2 => {
                v___x_3561_ = lean_box(0);
                if v_isShared_3560_ == 0 {
                    lean_ctor_set(v___x_3559_, 0, v___x_3561_);
                    v___x_3563_ = v___x_3559_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
                    v___x_3563_ = v_reuseFailAlloc_3564_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3563_;
            }
            4 => {
                v___x_3570_ = lean_box(0);
                if v_isShared_3569_ == 0 {
                    lean_ctor_set(v___x_3568_, 0, v___x_3570_);
                    v___x_3572_ = v___x_3568_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
                    v___x_3572_ = v_reuseFailAlloc_3573_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3572_;
            }
            6 => {
                v___x_3579_ = lean_box(0);
                if v_isShared_3578_ == 0 {
                    lean_ctor_set(v___x_3577_, 0, v___x_3579_);
                    v___x_3581_ = v___x_3577_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
                    v___x_3581_ = v_reuseFailAlloc_3582_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3581_;
            }
            8 => {
                v___x_3586_ = lean_box(0);
                v___x_3587_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3587_, 0, v___x_3586_);
                return v___x_3587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___boxed(
    mut v_x_3596_: *mut LeanObject,
    mut v_xType_3597_: *mut LeanObject,
    mut v_a_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3600_: *mut LeanObject = core::ptr::null_mut();
    v_res_3600_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_3596_, v_xType_3597_, v_a_3598_);
    lean_dec(v_a_3598_);
    lean_dec_ref(v_xType_3597_);
    lean_dec(v_x_3596_);
    return v_res_3600_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(
    mut v_x_3601_: *mut LeanObject,
    mut v_xType_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
    mut v_a_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
    mut v_a_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    v___x_3610_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_3601_, v_xType_3602_, v_a_3606_);
    return v___x_3610_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___boxed(
    mut v_x_3611_: *mut LeanObject,
    mut v_xType_3612_: *mut LeanObject,
    mut v_a_3613_: *mut LeanObject,
    mut v_a_3614_: *mut LeanObject,
    mut v_a_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
    mut v_a_3617_: *mut LeanObject,
    mut v_a_3618_: *mut LeanObject,
    mut v_a_3619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3620_: *mut LeanObject = core::ptr::null_mut();
    v_res_3620_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(v_x_3611_, v_xType_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
    lean_dec(v_a_3618_);
    lean_dec_ref(v_a_3617_);
    lean_dec(v_a_3616_);
    lean_dec_ref(v_a_3615_);
    lean_dec(v_a_3614_);
    lean_dec_ref(v_a_3613_);
    lean_dec_ref(v_xType_3612_);
    lean_dec(v_x_3611_);
    return v_res_3620_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(
    mut v_fvarId_3626_: *mut LeanObject,
    mut v_fvarIdType_3627_: *mut LeanObject,
    mut v_expectedType_3628_: *mut LeanObject,
    mut v_a_3629_: *mut LeanObject,
    mut v_a_3630_: *mut LeanObject,
    mut v_a_3631_: *mut LeanObject,
    mut v_a_3632_: *mut LeanObject,
    mut v_a_3633_: *mut LeanObject,
    mut v_a_3634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3649_: u8 = 0;
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currDecl_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextAuxIdx_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: u8 = 0;
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDecls_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextAuxIdx_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3697_: u8 = 0;
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut v_unused_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3707_: u8 = 0;
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3711_: u8 = 0;
    let mut v_reuseFailAlloc_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3713_: u8 = 0;
    let mut v_declName_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3718_: u8 = 0;
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3723_: u8 = 0;
    let mut v_unused_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3728_: u8 = 0;
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3732_: u8 = 0;
    let mut v_a_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3740_: u8 = 0;
    let mut v_reuseFailAlloc_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v_unused_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3748_: u8 = 0;
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3752_: u8 = 0;
    let mut v_a_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3760_: u8 = 0;
    let mut v_isSharedCheck_3761_: u8 = 0;
    let mut v_isSharedCheck_3762_: u8 = 0;
    let mut v_a_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3636_ =
                    l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_expectedType_3628_);
                if v___x_3636_ == 0 {
                    v___x_3637_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_fvarId_3626_, v_fvarIdType_3627_, v_a_3632_);
                    if lean_obj_tag(v___x_3637_) == 0 {
                        v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
                        v_isSharedCheck_3762_ = (!lean_is_exclusive(v___x_3637_)) as u8;
                        if v_isSharedCheck_3762_ == 0 {
                            v___x_3640_ = v___x_3637_;
                            v_isShared_3641_ = v_isSharedCheck_3762_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3638_);
                            lean_dec(v___x_3637_);
                            v___x_3640_ = lean_box(0);
                            v_isShared_3641_ = v_isSharedCheck_3762_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_expectedType_3628_);
                        lean_dec_ref(v_fvarIdType_3627_);
                        lean_dec(v_fvarId_3626_);
                        v_a_3763_ = lean_ctor_get(v___x_3637_, 0);
                        v_isSharedCheck_3770_ = (!lean_is_exclusive(v___x_3637_)) as u8;
                        if v_isSharedCheck_3770_ == 0 {
                            v___x_3765_ = v___x_3637_;
                            v_isShared_3766_ = v_isSharedCheck_3770_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_3763_);
                            lean_dec(v___x_3637_);
                            v___x_3765_ = lean_box(0);
                            v_isShared_3766_ = v_isSharedCheck_3770_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_expectedType_3628_);
                    lean_dec_ref(v_fvarIdType_3627_);
                    v___x_3771_ = lean_alloc_ctor(14, 1, (0) as u32);
                    lean_ctor_set(v___x_3771_, 0, v_fvarId_3626_);
                    v___x_3772_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3772_, 0, v___x_3771_);
                    return v___x_3772_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_3638_) == 0 {
                    lean_dec_ref(v_expectedType_3628_);
                    v___x_3642_ = lean_alloc_ctor(13, 2, (0) as u32);
                    lean_ctor_set(v___x_3642_, 0, v_fvarIdType_3627_);
                    lean_ctor_set(v___x_3642_, 1, v_fvarId_3626_);
                    if v_isShared_3641_ == 0 {
                        lean_ctor_set(v___x_3640_, 0, v___x_3642_);
                        v___x_3644_ = v___x_3640_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
                        v___x_3644_ = v_reuseFailAlloc_3645_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3640_);
                    lean_dec(v_fvarId_3626_);
                    v_val_3646_ = lean_ctor_get(v_a_3638_, 0);
                    v_isSharedCheck_3761_ = (!lean_is_exclusive(v_a_3638_)) as u8;
                    if v_isSharedCheck_3761_ == 0 {
                        v___x_3648_ = v_a_3638_;
                        v_isShared_3649_ = v_isSharedCheck_3761_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_3646_);
                        lean_dec(v_a_3638_);
                        v___x_3648_ = lean_box(0);
                        v_isShared_3649_ = v_isSharedCheck_3761_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3644_;
            }
            3 => {
                v___x_3650_ = 1;
                v___x_3651_ = lean_box(0);
                lean_inc_ref(v_fvarIdType_3627_);
                v___x_3652_ = l_Lean_Compiler_LCNF_mkLetDecl(
                    v___x_3650_,
                    v___x_3651_,
                    v_fvarIdType_3627_,
                    v_val_3646_,
                    v_a_3631_,
                    v_a_3632_,
                    v_a_3633_,
                    v_a_3634_,
                );
                if lean_obj_tag(v___x_3652_) == 0 {
                    v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
                    lean_inc(v_a_3653_);
                    lean_dec_ref_known(v___x_3652_, 1);
                    v_fvarId_3654_ = lean_ctor_get(v_a_3653_, 0);
                    lean_inc(v_fvarId_3654_);
                    v___x_3655_ = lean_alloc_ctor(13, 2, (0) as u32);
                    lean_ctor_set(v___x_3655_, 0, v_fvarIdType_3627_);
                    lean_ctor_set(v___x_3655_, 1, v_fvarId_3654_);
                    lean_inc_ref(v_expectedType_3628_);
                    v___x_3656_ = l_Lean_Compiler_LCNF_mkLetDecl(
                        v___x_3650_,
                        v___x_3651_,
                        v_expectedType_3628_,
                        v___x_3655_,
                        v_a_3631_,
                        v_a_3632_,
                        v_a_3633_,
                        v_a_3634_,
                    );
                    if lean_obj_tag(v___x_3656_) == 0 {
                        v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
                        lean_inc(v_a_3657_);
                        lean_dec_ref_known(v___x_3656_, 1);
                        v_fvarId_3658_ = lean_ctor_get(v_a_3657_, 0);
                        v___x_3659_ = lean_st_ref_get(v_a_3630_);
                        v_currDecl_3660_ = lean_ctor_get(v_a_3629_, 0);
                        v_nextAuxIdx_3661_ = lean_ctor_get(v___x_3659_, 1);
                        v_isSharedCheck_3743_ = (!lean_is_exclusive(v___x_3659_)) as u8;
                        if v_isSharedCheck_3743_ == 0 {
                            v_unused_3744_ = lean_ctor_get(v___x_3659_, 0);
                            lean_dec(v_unused_3744_);
                            v___x_3663_ = v___x_3659_;
                            v_isShared_3664_ = v_isSharedCheck_3743_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_nextAuxIdx_3661_);
                            lean_dec(v___x_3659_);
                            v___x_3663_ = lean_box(0);
                            v_isShared_3664_ = v_isSharedCheck_3743_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3653_);
                        lean_del_object(v___x_3648_);
                        lean_dec_ref(v_expectedType_3628_);
                        v_a_3745_ = lean_ctor_get(v___x_3656_, 0);
                        v_isSharedCheck_3752_ = (!lean_is_exclusive(v___x_3656_)) as u8;
                        if v_isSharedCheck_3752_ == 0 {
                            v___x_3747_ = v___x_3656_;
                            v_isShared_3748_ = v_isSharedCheck_3752_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_3745_);
                            lean_dec(v___x_3656_);
                            v___x_3747_ = lean_box(0);
                            v_isShared_3748_ = v_isSharedCheck_3752_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3648_);
                    lean_dec_ref(v_expectedType_3628_);
                    lean_dec_ref(v_fvarIdType_3627_);
                    v_a_3753_ = lean_ctor_get(v___x_3652_, 0);
                    v_isSharedCheck_3760_ = (!lean_is_exclusive(v___x_3652_)) as u8;
                    if v_isSharedCheck_3760_ == 0 {
                        v___x_3755_ = v___x_3652_;
                        v_isShared_3756_ = v_isSharedCheck_3760_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_3753_);
                        lean_dec(v___x_3652_);
                        v___x_3755_ = lean_box(0);
                        v_isShared_3756_ = v_isSharedCheck_3760_;
                        state = 21;
                        continue;
                    }
                }
            }
            4 => {
                lean_inc(v_fvarId_3658_);
                if v_isShared_3649_ == 0 {
                    lean_ctor_set_tag(v___x_3648_, 5);
                    lean_ctor_set(v___x_3648_, 0, v_fvarId_3658_);
                    v___x_3666_ = v___x_3648_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_fvarId_3658_);
                    v___x_3666_ = v_reuseFailAlloc_3742_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3664_ == 0 {
                    lean_ctor_set(v___x_3663_, 1, v___x_3666_);
                    lean_ctor_set(v___x_3663_, 0, v_a_3657_);
                    v___x_3668_ = v___x_3663_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3657_);
                    lean_ctor_set(v_reuseFailAlloc_3741_, 1, v___x_3666_);
                    v___x_3668_ = v_reuseFailAlloc_3741_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3669_ = 1;
                v___x_3670_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3670_, 0, v_a_3653_);
                lean_ctor_set(v___x_3670_, 1, v___x_3668_);
                v___x_3671_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1;
                v___x_3672_ = lean_name_append_index_after(v___x_3671_, v_nextAuxIdx_3661_);
                lean_inc(v_currDecl_3660_);
                v___x_3673_ = l_Lean_Name_append(v_currDecl_3660_, v___x_3672_);
                v___x_3674_ = lean_box(0);
                v___x_3675_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2;
                lean_inc(v___x_3673_);
                v___x_3676_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_3676_, 0, v___x_3673_);
                lean_ctor_set(v___x_3676_, 1, v___x_3674_);
                lean_ctor_set(v___x_3676_, 2, v_expectedType_3628_);
                lean_ctor_set(v___x_3676_, 3, v___x_3675_);
                lean_ctor_set_uint8(
                    v___x_3676_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___x_3669_,
                );
                v___x_3677_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3677_, 0, v___x_3670_);
                v___x_3678_ = lean_box(0);
                v___x_3679_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3679_, 0, v___x_3676_);
                lean_ctor_set(v___x_3679_, 1, v___x_3677_);
                lean_ctor_set(v___x_3679_, 2, v___x_3678_);
                lean_ctor_set_uint8(
                    v___x_3679_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3636_,
                );
                lean_inc_ref(v___x_3679_);
                v___x_3680_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(
                    v___x_3650_,
                    v___x_3679_,
                    v_a_3633_,
                    v_a_3634_,
                );
                if lean_obj_tag(v___x_3680_) == 0 {
                    v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
                    lean_inc(v_a_3681_);
                    lean_dec_ref_known(v___x_3680_, 1);
                    if lean_obj_tag(v_a_3681_) == 0 {
                        v___x_3682_ = lean_st_ref_take(v_a_3630_);
                        v_auxDecls_3683_ = lean_ctor_get(v___x_3682_, 0);
                        v_nextAuxIdx_3684_ = lean_ctor_get(v___x_3682_, 1);
                        v_isSharedCheck_3713_ = (!lean_is_exclusive(v___x_3682_)) as u8;
                        if v_isSharedCheck_3713_ == 0 {
                            v___x_3686_ = v___x_3682_;
                            v_isShared_3687_ = v_isSharedCheck_3713_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_nextAuxIdx_3684_);
                            lean_inc(v_auxDecls_3683_);
                            lean_dec(v___x_3682_);
                            v___x_3686_ = lean_box(0);
                            v_isShared_3687_ = v_isSharedCheck_3713_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3673_);
                        v_declName_3714_ = lean_ctor_get(v_a_3681_, 0);
                        lean_inc(v_declName_3714_);
                        lean_dec_ref_known(v_a_3681_, 1);
                        v___x_3715_ = l_Lean_Compiler_LCNF_eraseDecl(
                            v___x_3650_,
                            v___x_3679_,
                            v_a_3631_,
                            v_a_3632_,
                            v_a_3633_,
                            v_a_3634_,
                        );
                        if lean_obj_tag(v___x_3715_) == 0 {
                            v_isSharedCheck_3723_ = (!lean_is_exclusive(v___x_3715_)) as u8;
                            if v_isSharedCheck_3723_ == 0 {
                                v_unused_3724_ = lean_ctor_get(v___x_3715_, 0);
                                lean_dec(v_unused_3724_);
                                v___x_3717_ = v___x_3715_;
                                v_isShared_3718_ = v_isSharedCheck_3723_;
                                state = 13;
                                continue;
                            } else {
                                lean_dec(v___x_3715_);
                                v___x_3717_ = lean_box(0);
                                v_isShared_3718_ = v_isSharedCheck_3723_;
                                state = 13;
                                continue;
                            }
                        } else {
                            lean_dec(v_declName_3714_);
                            v_a_3725_ = lean_ctor_get(v___x_3715_, 0);
                            v_isSharedCheck_3732_ = (!lean_is_exclusive(v___x_3715_)) as u8;
                            if v_isSharedCheck_3732_ == 0 {
                                v___x_3727_ = v___x_3715_;
                                v_isShared_3728_ = v_isSharedCheck_3732_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_3725_);
                                lean_dec(v___x_3715_);
                                v___x_3727_ = lean_box(0);
                                v_isShared_3728_ = v_isSharedCheck_3732_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_3679_, 3);
                    lean_dec(v___x_3673_);
                    v_a_3733_ = lean_ctor_get(v___x_3680_, 0);
                    v_isSharedCheck_3740_ = (!lean_is_exclusive(v___x_3680_)) as u8;
                    if v_isSharedCheck_3740_ == 0 {
                        v___x_3735_ = v___x_3680_;
                        v_isShared_3736_ = v_isSharedCheck_3740_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3733_);
                        lean_dec(v___x_3680_);
                        v___x_3735_ = lean_box(0);
                        v_isShared_3736_ = v_isSharedCheck_3740_;
                        state = 17;
                        continue;
                    }
                }
            }
            7 => {
                lean_inc_ref(v___x_3679_);
                v___x_3688_ = lean_array_push(v_auxDecls_3683_, v___x_3679_);
                v___x_3689_ = lean_unsigned_to_nat(1);
                v___x_3690_ = lean_nat_add(v_nextAuxIdx_3684_, v___x_3689_);
                lean_dec(v_nextAuxIdx_3684_);
                if v_isShared_3687_ == 0 {
                    lean_ctor_set(v___x_3686_, 1, v___x_3690_);
                    lean_ctor_set(v___x_3686_, 0, v___x_3688_);
                    v___x_3692_ = v___x_3686_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3688_);
                    lean_ctor_set(v_reuseFailAlloc_3712_, 1, v___x_3690_);
                    v___x_3692_ = v_reuseFailAlloc_3712_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3693_ = lean_st_ref_set(v_a_3630_, v___x_3692_);
                v___x_3694_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_3679_, v_a_3634_);
                if lean_obj_tag(v___x_3694_) == 0 {
                    v_isSharedCheck_3702_ = (!lean_is_exclusive(v___x_3694_)) as u8;
                    if v_isSharedCheck_3702_ == 0 {
                        v_unused_3703_ = lean_ctor_get(v___x_3694_, 0);
                        lean_dec(v_unused_3703_);
                        v___x_3696_ = v___x_3694_;
                        v_isShared_3697_ = v_isSharedCheck_3702_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_3694_);
                        v___x_3696_ = lean_box(0);
                        v_isShared_3697_ = v_isSharedCheck_3702_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3673_);
                    v_a_3704_ = lean_ctor_get(v___x_3694_, 0);
                    v_isSharedCheck_3711_ = (!lean_is_exclusive(v___x_3694_)) as u8;
                    if v_isSharedCheck_3711_ == 0 {
                        v___x_3706_ = v___x_3694_;
                        v_isShared_3707_ = v_isSharedCheck_3711_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3704_);
                        lean_dec(v___x_3694_);
                        v___x_3706_ = lean_box(0);
                        v_isShared_3707_ = v_isSharedCheck_3711_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3698_ = lean_alloc_ctor(9, 2, (0) as u32);
                lean_ctor_set(v___x_3698_, 0, v___x_3673_);
                lean_ctor_set(v___x_3698_, 1, v___x_3675_);
                if v_isShared_3697_ == 0 {
                    lean_ctor_set(v___x_3696_, 0, v___x_3698_);
                    v___x_3700_ = v___x_3696_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3698_);
                    v___x_3700_ = v_reuseFailAlloc_3701_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3700_;
            }
            11 => {
                if v_isShared_3707_ == 0 {
                    v___x_3709_ = v___x_3706_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
                    v___x_3709_ = v_reuseFailAlloc_3710_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3709_;
            }
            13 => {
                v___x_3719_ = lean_alloc_ctor(9, 2, (0) as u32);
                lean_ctor_set(v___x_3719_, 0, v_declName_3714_);
                lean_ctor_set(v___x_3719_, 1, v___x_3675_);
                if v_isShared_3718_ == 0 {
                    lean_ctor_set(v___x_3717_, 0, v___x_3719_);
                    v___x_3721_ = v___x_3717_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
                    v___x_3721_ = v_reuseFailAlloc_3722_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3721_;
            }
            15 => {
                if v_isShared_3728_ == 0 {
                    v___x_3730_ = v___x_3727_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
                    v___x_3730_ = v_reuseFailAlloc_3731_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3730_;
            }
            17 => {
                if v_isShared_3736_ == 0 {
                    v___x_3738_ = v___x_3735_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
                    v___x_3738_ = v_reuseFailAlloc_3739_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3738_;
            }
            19 => {
                if v_isShared_3748_ == 0 {
                    v___x_3750_ = v___x_3747_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
                    v___x_3750_ = v_reuseFailAlloc_3751_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3750_;
            }
            21 => {
                if v_isShared_3756_ == 0 {
                    v___x_3758_ = v___x_3755_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
                    v___x_3758_ = v_reuseFailAlloc_3759_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3758_;
            }
            23 => {
                if v_isShared_3766_ == 0 {
                    v___x_3768_ = v___x_3765_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___boxed(
    mut v_fvarId_3773_: *mut LeanObject,
    mut v_fvarIdType_3774_: *mut LeanObject,
    mut v_expectedType_3775_: *mut LeanObject,
    mut v_a_3776_: *mut LeanObject,
    mut v_a_3777_: *mut LeanObject,
    mut v_a_3778_: *mut LeanObject,
    mut v_a_3779_: *mut LeanObject,
    mut v_a_3780_: *mut LeanObject,
    mut v_a_3781_: *mut LeanObject,
    mut v_a_3782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3783_: *mut LeanObject = core::ptr::null_mut();
    v_res_3783_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(
        v_fvarId_3773_,
        v_fvarIdType_3774_,
        v_expectedType_3775_,
        v_a_3776_,
        v_a_3777_,
        v_a_3778_,
        v_a_3779_,
        v_a_3780_,
        v_a_3781_,
    );
    lean_dec(v_a_3781_);
    lean_dec_ref(v_a_3780_);
    lean_dec(v_a_3779_);
    lean_dec_ref(v_a_3778_);
    lean_dec(v_a_3777_);
    lean_dec_ref(v_a_3776_);
    return v_res_3783_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(
    mut v_fvarId_3784_: *mut LeanObject,
    mut v_expectedType_3785_: *mut LeanObject,
    mut v_k_3786_: *mut LeanObject,
    mut v_a_3787_: *mut LeanObject,
    mut v_a_3788_: *mut LeanObject,
    mut v_a_3789_: *mut LeanObject,
    mut v_a_3790_: *mut LeanObject,
    mut v_a_3791_: *mut LeanObject,
    mut v_a_3792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: u8 = 0;
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: u8 = 0;
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3813_: u8 = 0;
    let mut v_a_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3817_: u8 = 0;
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut v_a_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3825_: u8 = 0;
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3834_: u8 = 0;
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_3784_);
                v___x_3794_ = l_Lean_Compiler_LCNF_getType(
                    v_fvarId_3784_,
                    v_a_3789_,
                    v_a_3790_,
                    v_a_3791_,
                    v_a_3792_,
                );
                if lean_obj_tag(v___x_3794_) == 0 {
                    v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
                    lean_inc(v_a_3795_);
                    lean_dec_ref_known(v___x_3794_, 1);
                    v___x_3796_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_3795_, v_expectedType_3785_);
                    if v___x_3796_ == 0 {
                        lean_inc_ref(v_expectedType_3785_);
                        v___x_3797_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_3784_, v_a_3795_, v_expectedType_3785_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
                        if lean_obj_tag(v___x_3797_) == 0 {
                            v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
                            lean_inc(v_a_3798_);
                            lean_dec_ref_known(v___x_3797_, 1);
                            v___x_3799_ = 1;
                            v___x_3800_ = lean_box(0);
                            v___x_3801_ = l_Lean_Compiler_LCNF_mkLetDecl(
                                v___x_3799_,
                                v___x_3800_,
                                v_expectedType_3785_,
                                v_a_3798_,
                                v_a_3789_,
                                v_a_3790_,
                                v_a_3791_,
                                v_a_3792_,
                            );
                            if lean_obj_tag(v___x_3801_) == 0 {
                                v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
                                lean_inc(v_a_3802_);
                                lean_dec_ref_known(v___x_3801_, 1);
                                v_fvarId_3803_ = lean_ctor_get(v_a_3802_, 0);
                                lean_inc(v_a_3792_);
                                lean_inc_ref(v_a_3791_);
                                lean_inc(v_a_3790_);
                                lean_inc_ref(v_a_3789_);
                                lean_inc(v_a_3788_);
                                lean_inc_ref(v_a_3787_);
                                lean_inc(v_fvarId_3803_);
                                v___x_3804_ = lean_apply_8(
                                    v_k_3786_,
                                    v_fvarId_3803_,
                                    v_a_3787_,
                                    v_a_3788_,
                                    v_a_3789_,
                                    v_a_3790_,
                                    v_a_3791_,
                                    v_a_3792_,
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_3804_) == 0 {
                                    v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
                                    v_isSharedCheck_3813_ = (!lean_is_exclusive(v___x_3804_)) as u8;
                                    if v_isSharedCheck_3813_ == 0 {
                                        v___x_3807_ = v___x_3804_;
                                        v_isShared_3808_ = v_isSharedCheck_3813_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3805_);
                                        lean_dec(v___x_3804_);
                                        v___x_3807_ = lean_box(0);
                                        v_isShared_3808_ = v_isSharedCheck_3813_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3802_);
                                    return v___x_3804_;
                                }
                            } else {
                                lean_dec_ref(v_k_3786_);
                                v_a_3814_ = lean_ctor_get(v___x_3801_, 0);
                                v_isSharedCheck_3821_ = (!lean_is_exclusive(v___x_3801_)) as u8;
                                if v_isSharedCheck_3821_ == 0 {
                                    v___x_3816_ = v___x_3801_;
                                    v_isShared_3817_ = v_isSharedCheck_3821_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_3814_);
                                    lean_dec(v___x_3801_);
                                    v___x_3816_ = lean_box(0);
                                    v_isShared_3817_ = v_isSharedCheck_3821_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_k_3786_);
                            lean_dec_ref(v_expectedType_3785_);
                            v_a_3822_ = lean_ctor_get(v___x_3797_, 0);
                            v_isSharedCheck_3829_ = (!lean_is_exclusive(v___x_3797_)) as u8;
                            if v_isSharedCheck_3829_ == 0 {
                                v___x_3824_ = v___x_3797_;
                                v_isShared_3825_ = v_isSharedCheck_3829_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3822_);
                                lean_dec(v___x_3797_);
                                v___x_3824_ = lean_box(0);
                                v_isShared_3825_ = v_isSharedCheck_3829_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3795_);
                        lean_dec_ref(v_expectedType_3785_);
                        lean_inc(v_a_3792_);
                        lean_inc_ref(v_a_3791_);
                        lean_inc(v_a_3790_);
                        lean_inc_ref(v_a_3789_);
                        lean_inc(v_a_3788_);
                        lean_inc_ref(v_a_3787_);
                        v___x_3830_ = lean_apply_8(
                            v_k_3786_,
                            v_fvarId_3784_,
                            v_a_3787_,
                            v_a_3788_,
                            v_a_3789_,
                            v_a_3790_,
                            v_a_3791_,
                            v_a_3792_,
                            lean_box(0),
                        );
                        return v___x_3830_;
                    }
                } else {
                    lean_dec_ref(v_k_3786_);
                    lean_dec_ref(v_expectedType_3785_);
                    lean_dec(v_fvarId_3784_);
                    v_a_3831_ = lean_ctor_get(v___x_3794_, 0);
                    v_isSharedCheck_3838_ = (!lean_is_exclusive(v___x_3794_)) as u8;
                    if v_isSharedCheck_3838_ == 0 {
                        v___x_3833_ = v___x_3794_;
                        v_isShared_3834_ = v_isSharedCheck_3838_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3831_);
                        lean_dec(v___x_3794_);
                        v___x_3833_ = lean_box(0);
                        v_isShared_3834_ = v_isSharedCheck_3838_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3809_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3809_, 0, v_a_3802_);
                lean_ctor_set(v___x_3809_, 1, v_a_3805_);
                if v_isShared_3808_ == 0 {
                    lean_ctor_set(v___x_3807_, 0, v___x_3809_);
                    v___x_3811_ = v___x_3807_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
                    v___x_3811_ = v_reuseFailAlloc_3812_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3811_;
            }
            3 => {
                if v_isShared_3817_ == 0 {
                    v___x_3819_ = v___x_3816_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
                    v___x_3819_ = v_reuseFailAlloc_3820_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3819_;
            }
            5 => {
                if v_isShared_3825_ == 0 {
                    v___x_3827_ = v___x_3824_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
                    v___x_3827_ = v_reuseFailAlloc_3828_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3827_;
            }
            7 => {
                if v_isShared_3834_ == 0 {
                    v___x_3836_ = v___x_3833_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
                    v___x_3836_ = v_reuseFailAlloc_3837_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded___boxed(
    mut v_fvarId_3839_: *mut LeanObject,
    mut v_expectedType_3840_: *mut LeanObject,
    mut v_k_3841_: *mut LeanObject,
    mut v_a_3842_: *mut LeanObject,
    mut v_a_3843_: *mut LeanObject,
    mut v_a_3844_: *mut LeanObject,
    mut v_a_3845_: *mut LeanObject,
    mut v_a_3846_: *mut LeanObject,
    mut v_a_3847_: *mut LeanObject,
    mut v_a_3848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3849_: *mut LeanObject = core::ptr::null_mut();
    v_res_3849_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(
            v_fvarId_3839_,
            v_expectedType_3840_,
            v_k_3841_,
            v_a_3842_,
            v_a_3843_,
            v_a_3844_,
            v_a_3845_,
            v_a_3846_,
            v_a_3847_,
        );
    lean_dec(v_a_3847_);
    lean_dec_ref(v_a_3846_);
    lean_dec(v_a_3845_);
    lean_dec_ref(v_a_3844_);
    lean_dec(v_a_3843_);
    lean_dec_ref(v_a_3842_);
    return v_res_3849_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(
    mut v_arg_3850_: *mut LeanObject,
    mut v_k_3851_: *mut LeanObject,
    mut v_x_3852_: *mut LeanObject,
    mut v___y_3853_: *mut LeanObject,
    mut v___y_3854_: *mut LeanObject,
    mut v___y_3855_: *mut LeanObject,
    mut v___y_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    v___x_3860_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(
            v_arg_3850_,
            v_x_3852_,
        );
    lean_inc(v___y_3858_);
    lean_inc_ref(v___y_3857_);
    lean_inc(v___y_3856_);
    lean_inc_ref(v___y_3855_);
    lean_inc(v___y_3854_);
    lean_inc_ref(v___y_3853_);
    v___x_3861_ = lean_apply_8(
        v_k_3851_,
        v___x_3860_,
        v___y_3853_,
        v___y_3854_,
        v___y_3855_,
        v___y_3856_,
        v___y_3857_,
        v___y_3858_,
        lean_box(0),
    );
    return v___x_3861_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0___boxed(
    mut v_arg_3862_: *mut LeanObject,
    mut v_k_3863_: *mut LeanObject,
    mut v_x_3864_: *mut LeanObject,
    mut v___y_3865_: *mut LeanObject,
    mut v___y_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
    mut v___y_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3872_: *mut LeanObject = core::ptr::null_mut();
    v_res_3872_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_3862_, v_k_3863_, v_x_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
    lean_dec(v___y_3870_);
    lean_dec_ref(v___y_3869_);
    lean_dec(v___y_3868_);
    lean_dec_ref(v___y_3867_);
    lean_dec(v___y_3866_);
    lean_dec_ref(v___y_3865_);
    return v_res_3872_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(
    mut v_arg_3873_: *mut LeanObject,
    mut v_expectedType_3874_: *mut LeanObject,
    mut v_k_3875_: *mut LeanObject,
    mut v_a_3876_: *mut LeanObject,
    mut v_a_3877_: *mut LeanObject,
    mut v_a_3878_: *mut LeanObject,
    mut v_a_3879_: *mut LeanObject,
    mut v_a_3880_: *mut LeanObject,
    mut v_a_3881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: u8 = 0;
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3904_: u8 = 0;
    let mut v_a_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3908_: u8 = 0;
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut v_a_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3916_: u8 = 0;
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3920_: u8 = 0;
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_arg_3873_) == 0 {
                    lean_dec_ref(v_expectedType_3874_);
                    lean_inc(v_a_3881_);
                    lean_inc_ref(v_a_3880_);
                    lean_inc(v_a_3879_);
                    lean_inc_ref(v_a_3878_);
                    lean_inc(v_a_3877_);
                    lean_inc_ref(v_a_3876_);
                    v___x_3883_ = lean_apply_8(
                        v_k_3875_,
                        v_arg_3873_,
                        v_a_3876_,
                        v_a_3877_,
                        v_a_3878_,
                        v_a_3879_,
                        v_a_3880_,
                        v_a_3881_,
                        lean_box(0),
                    );
                    return v___x_3883_;
                } else {
                    v_fvarId_3884_ = lean_ctor_get(v_arg_3873_, 0);
                    lean_inc(v_fvarId_3884_);
                    v___x_3885_ = l_Lean_Compiler_LCNF_getType(
                        v_fvarId_3884_,
                        v_a_3878_,
                        v_a_3879_,
                        v_a_3880_,
                        v_a_3881_,
                    );
                    if lean_obj_tag(v___x_3885_) == 0 {
                        v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
                        lean_inc(v_a_3886_);
                        lean_dec_ref_known(v___x_3885_, 1);
                        v___x_3887_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_3886_, v_expectedType_3874_);
                        if v___x_3887_ == 0 {
                            lean_inc_ref(v_expectedType_3874_);
                            lean_inc(v_fvarId_3884_);
                            v___x_3888_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_3884_, v_a_3886_, v_expectedType_3874_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
                            if lean_obj_tag(v___x_3888_) == 0 {
                                v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
                                lean_inc(v_a_3889_);
                                lean_dec_ref_known(v___x_3888_, 1);
                                v___x_3890_ = 1;
                                v___x_3891_ = lean_box(0);
                                v___x_3892_ = l_Lean_Compiler_LCNF_mkLetDecl(
                                    v___x_3890_,
                                    v___x_3891_,
                                    v_expectedType_3874_,
                                    v_a_3889_,
                                    v_a_3878_,
                                    v_a_3879_,
                                    v_a_3880_,
                                    v_a_3881_,
                                );
                                if lean_obj_tag(v___x_3892_) == 0 {
                                    v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
                                    lean_inc(v_a_3893_);
                                    lean_dec_ref_known(v___x_3892_, 1);
                                    v_fvarId_3894_ = lean_ctor_get(v_a_3893_, 0);
                                    lean_inc(v_fvarId_3894_);
                                    v___x_3895_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_3873_, v_k_3875_, v_fvarId_3894_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
                                    if lean_obj_tag(v___x_3895_) == 0 {
                                        v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
                                        v_isSharedCheck_3904_ =
                                            (!lean_is_exclusive(v___x_3895_)) as u8;
                                        if v_isSharedCheck_3904_ == 0 {
                                            v___x_3898_ = v___x_3895_;
                                            v_isShared_3899_ = v_isSharedCheck_3904_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3896_);
                                            lean_dec(v___x_3895_);
                                            v___x_3898_ = lean_box(0);
                                            v_isShared_3899_ = v_isSharedCheck_3904_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_3893_);
                                        return v___x_3895_;
                                    }
                                } else {
                                    lean_dec_ref_known(v_arg_3873_, 1);
                                    lean_dec_ref(v_k_3875_);
                                    v_a_3905_ = lean_ctor_get(v___x_3892_, 0);
                                    v_isSharedCheck_3912_ = (!lean_is_exclusive(v___x_3892_)) as u8;
                                    if v_isSharedCheck_3912_ == 0 {
                                        v___x_3907_ = v___x_3892_;
                                        v_isShared_3908_ = v_isSharedCheck_3912_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3905_);
                                        lean_dec(v___x_3892_);
                                        v___x_3907_ = lean_box(0);
                                        v_isShared_3908_ = v_isSharedCheck_3912_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref_known(v_arg_3873_, 1);
                                lean_dec_ref(v_k_3875_);
                                lean_dec_ref(v_expectedType_3874_);
                                v_a_3913_ = lean_ctor_get(v___x_3888_, 0);
                                v_isSharedCheck_3920_ = (!lean_is_exclusive(v___x_3888_)) as u8;
                                if v_isSharedCheck_3920_ == 0 {
                                    v___x_3915_ = v___x_3888_;
                                    v_isShared_3916_ = v_isSharedCheck_3920_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_3913_);
                                    lean_dec(v___x_3888_);
                                    v___x_3915_ = lean_box(0);
                                    v_isShared_3916_ = v_isSharedCheck_3920_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc(v_fvarId_3884_);
                            lean_dec(v_a_3886_);
                            lean_dec_ref(v_expectedType_3874_);
                            v___x_3921_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_3873_, v_k_3875_, v_fvarId_3884_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
                            return v___x_3921_;
                        }
                    } else {
                        lean_dec_ref_known(v_arg_3873_, 1);
                        lean_dec_ref(v_k_3875_);
                        lean_dec_ref(v_expectedType_3874_);
                        v_a_3922_ = lean_ctor_get(v___x_3885_, 0);
                        v_isSharedCheck_3929_ = (!lean_is_exclusive(v___x_3885_)) as u8;
                        if v_isSharedCheck_3929_ == 0 {
                            v___x_3924_ = v___x_3885_;
                            v_isShared_3925_ = v_isSharedCheck_3929_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3922_);
                            lean_dec(v___x_3885_);
                            v___x_3924_ = lean_box(0);
                            v_isShared_3925_ = v_isSharedCheck_3929_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3900_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3900_, 0, v_a_3893_);
                lean_ctor_set(v___x_3900_, 1, v_a_3896_);
                if v_isShared_3899_ == 0 {
                    lean_ctor_set(v___x_3898_, 0, v___x_3900_);
                    v___x_3902_ = v___x_3898_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3902_;
            }
            3 => {
                if v_isShared_3908_ == 0 {
                    v___x_3910_ = v___x_3907_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
                    v___x_3910_ = v_reuseFailAlloc_3911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3910_;
            }
            5 => {
                if v_isShared_3916_ == 0 {
                    v___x_3918_ = v___x_3915_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
                    v___x_3918_ = v_reuseFailAlloc_3919_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3918_;
            }
            7 => {
                if v_isShared_3925_ == 0 {
                    v___x_3927_ = v___x_3924_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
                    v___x_3927_ = v_reuseFailAlloc_3928_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___boxed(
    mut v_arg_3930_: *mut LeanObject,
    mut v_expectedType_3931_: *mut LeanObject,
    mut v_k_3932_: *mut LeanObject,
    mut v_a_3933_: *mut LeanObject,
    mut v_a_3934_: *mut LeanObject,
    mut v_a_3935_: *mut LeanObject,
    mut v_a_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3940_: *mut LeanObject = core::ptr::null_mut();
    v_res_3940_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(
            v_arg_3930_,
            v_expectedType_3931_,
            v_k_3932_,
            v_a_3933_,
            v_a_3934_,
            v_a_3935_,
            v_a_3936_,
            v_a_3937_,
            v_a_3938_,
        );
    lean_dec(v_a_3938_);
    lean_dec_ref(v_a_3937_);
    lean_dec(v_a_3936_);
    lean_dec_ref(v_a_3935_);
    lean_dec(v_a_3934_);
    lean_dec_ref(v_a_3933_);
    return v_res_3940_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(
    mut v_upperBound_3941_: *mut LeanObject,
    mut v_args_3942_: *mut LeanObject,
    mut v_typeFromIdx_3943_: *mut LeanObject,
    mut v_a_3944_: *mut LeanObject,
    mut v_b_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
    mut v___y_3947_: *mut LeanObject,
    mut v___y_3948_: *mut LeanObject,
    mut v___y_3949_: *mut LeanObject,
    mut v___y_3950_: *mut LeanObject,
    mut v___y_3951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: u8 = 0;
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: u8 = 0;
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3977_: u8 = 0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: u8 = 0;
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3997_: u8 = 0;
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4001_: u8 = 0;
    let mut v_a_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4005_: u8 = 0;
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut v_isSharedCheck_4010_: u8 = 0;
    let mut v_unused_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4019_: u8 = 0;
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut v_isSharedCheck_4024_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3958_ = lean_nat_dec_lt(v_a_3944_, v_upperBound_3941_);
                if v___x_3958_ == 0 {
                    lean_dec(v_a_3944_);
                    lean_dec_ref(v_typeFromIdx_3943_);
                    v___x_3959_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3959_, 0, v_b_3945_);
                    return v___x_3959_;
                } else {
                    v_fst_3960_ = lean_ctor_get(v_b_3945_, 0);
                    v_snd_3961_ = lean_ctor_get(v_b_3945_, 1);
                    v_isSharedCheck_4024_ = (!lean_is_exclusive(v_b_3945_)) as u8;
                    if v_isSharedCheck_4024_ == 0 {
                        v___x_3963_ = v_b_3945_;
                        v_isShared_3964_ = v_isSharedCheck_4024_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3961_);
                        lean_inc(v_fst_3960_);
                        lean_dec(v_b_3945_);
                        v___x_3963_ = lean_box(0);
                        v_isShared_3964_ = v_isSharedCheck_4024_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3955_ = lean_unsigned_to_nat(1);
                v___x_3956_ = lean_nat_add(v_a_3944_, v___x_3955_);
                lean_dec(v_a_3944_);
                v_a_3944_ = v___x_3956_;
                v_b_3945_ = v_a_3954_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3965_ = lean_array_fget(v_args_3942_, v_a_3944_);
                if lean_obj_tag(v___x_3965_) == 0 {
                    v___x_3966_ = lean_array_push(v_fst_3960_, v___x_3965_);
                    if v_isShared_3964_ == 0 {
                        lean_ctor_set(v___x_3963_, 0, v___x_3966_);
                        v___x_3968_ = v___x_3963_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
                        lean_ctor_set(v_reuseFailAlloc_3969_, 1, v_snd_3961_);
                        v___x_3968_ = v_reuseFailAlloc_3969_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_fvarId_3970_ = lean_ctor_get(v___x_3965_, 0);
                    lean_inc(v_fvarId_3970_);
                    v___x_3971_ = l_Lean_Compiler_LCNF_getType(
                        v_fvarId_3970_,
                        v___y_3948_,
                        v___y_3949_,
                        v___y_3950_,
                        v___y_3951_,
                    );
                    if lean_obj_tag(v___x_3971_) == 0 {
                        v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
                        lean_inc(v_a_3972_);
                        lean_dec_ref_known(v___x_3971_, 1);
                        lean_inc_ref(v_typeFromIdx_3943_);
                        lean_inc(v_a_3944_);
                        v___x_3973_ = lean_apply_1(v_typeFromIdx_3943_, v_a_3944_);
                        v___x_3974_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_3972_, v___x_3973_);
                        if v___x_3974_ == 0 {
                            lean_inc(v_fvarId_3970_);
                            v_isSharedCheck_4010_ = (!lean_is_exclusive(v___x_3965_)) as u8;
                            if v_isSharedCheck_4010_ == 0 {
                                v_unused_4011_ = lean_ctor_get(v___x_3965_, 0);
                                lean_dec(v_unused_4011_);
                                v___x_3976_ = v___x_3965_;
                                v_isShared_3977_ = v_isSharedCheck_4010_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v___x_3965_);
                                v___x_3976_ = lean_box(0);
                                v_isShared_3977_ = v_isSharedCheck_4010_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_3973_);
                            lean_dec(v_a_3972_);
                            v___x_4012_ = lean_array_push(v_fst_3960_, v___x_3965_);
                            if v_isShared_3964_ == 0 {
                                lean_ctor_set(v___x_3963_, 0, v___x_4012_);
                                v___x_4014_ = v___x_3963_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
                                lean_ctor_set(v_reuseFailAlloc_4015_, 1, v_snd_3961_);
                                v___x_4014_ = v_reuseFailAlloc_4015_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v___x_3965_, 1);
                        lean_del_object(v___x_3963_);
                        lean_dec(v_snd_3961_);
                        lean_dec(v_fst_3960_);
                        lean_dec(v_a_3944_);
                        lean_dec_ref(v_typeFromIdx_3943_);
                        v_a_4016_ = lean_ctor_get(v___x_3971_, 0);
                        v_isSharedCheck_4023_ = (!lean_is_exclusive(v___x_3971_)) as u8;
                        if v_isSharedCheck_4023_ == 0 {
                            v___x_4018_ = v___x_3971_;
                            v_isShared_4019_ = v_isSharedCheck_4023_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_4016_);
                            lean_dec(v___x_3971_);
                            v___x_4018_ = lean_box(0);
                            v_isShared_4019_ = v_isSharedCheck_4023_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_3954_ = v___x_3968_;
                state = 1;
                continue;
            }
            4 => {
                lean_inc_ref(v___x_3973_);
                v___x_3978_ =
                    l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(
                        v_fvarId_3970_,
                        v_a_3972_,
                        v___x_3973_,
                        v___y_3946_,
                        v___y_3947_,
                        v___y_3948_,
                        v___y_3949_,
                        v___y_3950_,
                        v___y_3951_,
                    );
                if lean_obj_tag(v___x_3978_) == 0 {
                    v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
                    lean_inc(v_a_3979_);
                    lean_dec_ref_known(v___x_3978_, 1);
                    v___x_3980_ = 1;
                    v___x_3981_ = lean_box(0);
                    v___x_3982_ = l_Lean_Compiler_LCNF_mkLetDecl(
                        v___x_3980_,
                        v___x_3981_,
                        v___x_3973_,
                        v_a_3979_,
                        v___y_3948_,
                        v___y_3949_,
                        v___y_3950_,
                        v___y_3951_,
                    );
                    if lean_obj_tag(v___x_3982_) == 0 {
                        v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
                        lean_inc(v_a_3983_);
                        lean_dec_ref_known(v___x_3982_, 1);
                        v_fvarId_3984_ = lean_ctor_get(v_a_3983_, 0);
                        lean_inc(v_fvarId_3984_);
                        if v_isShared_3977_ == 0 {
                            lean_ctor_set(v___x_3976_, 0, v_fvarId_3984_);
                            v___x_3986_ = v___x_3976_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_fvarId_3984_);
                            v___x_3986_ = v_reuseFailAlloc_3993_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3976_);
                        lean_del_object(v___x_3963_);
                        lean_dec(v_snd_3961_);
                        lean_dec(v_fst_3960_);
                        lean_dec(v_a_3944_);
                        lean_dec_ref(v_typeFromIdx_3943_);
                        v_a_3994_ = lean_ctor_get(v___x_3982_, 0);
                        v_isSharedCheck_4001_ = (!lean_is_exclusive(v___x_3982_)) as u8;
                        if v_isSharedCheck_4001_ == 0 {
                            v___x_3996_ = v___x_3982_;
                            v_isShared_3997_ = v_isSharedCheck_4001_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3994_);
                            lean_dec(v___x_3982_);
                            v___x_3996_ = lean_box(0);
                            v_isShared_3997_ = v_isSharedCheck_4001_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3976_);
                    lean_dec_ref(v___x_3973_);
                    lean_del_object(v___x_3963_);
                    lean_dec(v_snd_3961_);
                    lean_dec(v_fst_3960_);
                    lean_dec(v_a_3944_);
                    lean_dec_ref(v_typeFromIdx_3943_);
                    v_a_4002_ = lean_ctor_get(v___x_3978_, 0);
                    v_isSharedCheck_4009_ = (!lean_is_exclusive(v___x_3978_)) as u8;
                    if v_isSharedCheck_4009_ == 0 {
                        v___x_4004_ = v___x_3978_;
                        v_isShared_4005_ = v_isSharedCheck_4009_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4002_);
                        lean_dec(v___x_3978_);
                        v___x_4004_ = lean_box(0);
                        v_isShared_4005_ = v_isSharedCheck_4009_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3987_ = lean_array_push(v_fst_3960_, v___x_3986_);
                v___x_3988_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3988_, 0, v_a_3983_);
                v___x_3989_ = lean_array_push(v_snd_3961_, v___x_3988_);
                if v_isShared_3964_ == 0 {
                    lean_ctor_set(v___x_3963_, 1, v___x_3989_);
                    lean_ctor_set(v___x_3963_, 0, v___x_3987_);
                    v___x_3991_ = v___x_3963_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3987_);
                    lean_ctor_set(v_reuseFailAlloc_3992_, 1, v___x_3989_);
                    v___x_3991_ = v_reuseFailAlloc_3992_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_3954_ = v___x_3991_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_3997_ == 0 {
                    v___x_3999_ = v___x_3996_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
                    v___x_3999_ = v_reuseFailAlloc_4000_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3999_;
            }
            9 => {
                if v_isShared_4005_ == 0 {
                    v___x_4007_ = v___x_4004_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
                    v___x_4007_ = v_reuseFailAlloc_4008_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4007_;
            }
            11 => {
                v_a_3954_ = v___x_4014_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_4019_ == 0 {
                    v___x_4021_ = v___x_4018_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
                    v___x_4021_ = v_reuseFailAlloc_4022_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg___boxed(
    mut v_upperBound_4025_: *mut LeanObject,
    mut v_args_4026_: *mut LeanObject,
    mut v_typeFromIdx_4027_: *mut LeanObject,
    mut v_a_4028_: *mut LeanObject,
    mut v_b_4029_: *mut LeanObject,
    mut v___y_4030_: *mut LeanObject,
    mut v___y_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
    mut v___y_4036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4037_: *mut LeanObject = core::ptr::null_mut();
    v_res_4037_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_4025_, v_args_4026_, v_typeFromIdx_4027_, v_a_4028_, v_b_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
    lean_dec(v___y_4035_);
    lean_dec_ref(v___y_4034_);
    lean_dec(v___y_4033_);
    lean_dec_ref(v___y_4032_);
    lean_dec(v___y_4031_);
    lean_dec_ref(v___y_4030_);
    lean_dec_ref(v_args_4026_);
    lean_dec(v_upperBound_4025_);
    return v_res_4037_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(
    mut v_args_4038_: *mut LeanObject,
    mut v_typeFromIdx_4039_: *mut LeanObject,
    mut v_a_4040_: *mut LeanObject,
    mut v_a_4041_: *mut LeanObject,
    mut v_a_4042_: *mut LeanObject,
    mut v_a_4043_: *mut LeanObject,
    mut v_a_4044_: *mut LeanObject,
    mut v_a_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newArgs_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_casters_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v_fst_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4061_: u8 = 0;
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut v_isSharedCheck_4069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4047_ = lean_array_get_size(v_args_4038_);
                v_newArgs_4048_ = lean_mk_empty_array_with_capacity(v___x_4047_);
                v___x_4049_ = lean_unsigned_to_nat(0);
                v_casters_4050_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0;
                v___x_4051_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4051_, 0, v_newArgs_4048_);
                lean_ctor_set(v___x_4051_, 1, v_casters_4050_);
                v___x_4052_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v___x_4047_, v_args_4038_, v_typeFromIdx_4039_, v___x_4049_, v___x_4051_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
                if lean_obj_tag(v___x_4052_) == 0 {
                    v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
                    v_isSharedCheck_4069_ = (!lean_is_exclusive(v___x_4052_)) as u8;
                    if v_isSharedCheck_4069_ == 0 {
                        v___x_4055_ = v___x_4052_;
                        v_isShared_4056_ = v_isSharedCheck_4069_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4053_);
                        lean_dec(v___x_4052_);
                        v___x_4055_ = lean_box(0);
                        v_isShared_4056_ = v_isSharedCheck_4069_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4052_;
                }
            }
            1 => {
                v_fst_4057_ = lean_ctor_get(v_a_4053_, 0);
                v_snd_4058_ = lean_ctor_get(v_a_4053_, 1);
                v_isSharedCheck_4068_ = (!lean_is_exclusive(v_a_4053_)) as u8;
                if v_isSharedCheck_4068_ == 0 {
                    v___x_4060_ = v_a_4053_;
                    v_isShared_4061_ = v_isSharedCheck_4068_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4058_);
                    lean_inc(v_fst_4057_);
                    lean_dec(v_a_4053_);
                    v___x_4060_ = lean_box(0);
                    v_isShared_4061_ = v_isSharedCheck_4068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4061_ == 0 {
                    v___x_4063_ = v___x_4060_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_fst_4057_);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 1, v_snd_4058_);
                    v___x_4063_ = v_reuseFailAlloc_4067_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4056_ == 0 {
                    lean_ctor_set(v___x_4055_, 0, v___x_4063_);
                    v___x_4065_ = v___x_4055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4063_);
                    v___x_4065_ = v_reuseFailAlloc_4066_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux___boxed(
    mut v_args_4070_: *mut LeanObject,
    mut v_typeFromIdx_4071_: *mut LeanObject,
    mut v_a_4072_: *mut LeanObject,
    mut v_a_4073_: *mut LeanObject,
    mut v_a_4074_: *mut LeanObject,
    mut v_a_4075_: *mut LeanObject,
    mut v_a_4076_: *mut LeanObject,
    mut v_a_4077_: *mut LeanObject,
    mut v_a_4078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4079_: *mut LeanObject = core::ptr::null_mut();
    v_res_4079_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(
            v_args_4070_,
            v_typeFromIdx_4071_,
            v_a_4072_,
            v_a_4073_,
            v_a_4074_,
            v_a_4075_,
            v_a_4076_,
            v_a_4077_,
        );
    lean_dec(v_a_4077_);
    lean_dec_ref(v_a_4076_);
    lean_dec(v_a_4075_);
    lean_dec_ref(v_a_4074_);
    lean_dec(v_a_4073_);
    lean_dec_ref(v_a_4072_);
    lean_dec_ref(v_args_4070_);
    return v_res_4079_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(
    mut v_upperBound_4080_: *mut LeanObject,
    mut v_args_4081_: *mut LeanObject,
    mut v_typeFromIdx_4082_: *mut LeanObject,
    mut v_inst_4083_: *mut LeanObject,
    mut v_R_4084_: *mut LeanObject,
    mut v_a_4085_: *mut LeanObject,
    mut v_b_4086_: *mut LeanObject,
    mut v_c_4087_: *mut LeanObject,
    mut v___y_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
    mut v___y_4093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_4080_, v_args_4081_, v_typeFromIdx_4082_, v_a_4085_, v_b_4086_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
    return v___x_4095_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___boxed(
    mut v_upperBound_4096_: *mut LeanObject,
    mut v_args_4097_: *mut LeanObject,
    mut v_typeFromIdx_4098_: *mut LeanObject,
    mut v_inst_4099_: *mut LeanObject,
    mut v_R_4100_: *mut LeanObject,
    mut v_a_4101_: *mut LeanObject,
    mut v_b_4102_: *mut LeanObject,
    mut v_c_4103_: *mut LeanObject,
    mut v___y_4104_: *mut LeanObject,
    mut v___y_4105_: *mut LeanObject,
    mut v___y_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4111_: *mut LeanObject = core::ptr::null_mut();
    v_res_4111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(v_upperBound_4096_, v_args_4097_, v_typeFromIdx_4098_, v_inst_4099_, v_R_4100_, v_a_4101_, v_b_4102_, v_c_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
    lean_dec(v___y_4109_);
    lean_dec_ref(v___y_4108_);
    lean_dec(v___y_4107_);
    lean_dec_ref(v___y_4106_);
    lean_dec(v___y_4105_);
    lean_dec_ref(v___y_4104_);
    lean_dec_ref(v_args_4097_);
    lean_dec(v_upperBound_4096_);
    return v_res_4111_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4112_: u8 = 0;
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    v___x_4112_ = 1;
    v___x_4113_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_4112_);
    return v___x_4113_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(
    mut v_ps_4114_: *mut LeanObject,
    mut v_i_4115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4118_: *mut LeanObject = core::ptr::null_mut();
    v___x_4116_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
    v___x_4117_ = lean_array_get_borrowed(v___x_4116_, v_ps_4114_, v_i_4115_);
    v_type_4118_ = lean_ctor_get(v___x_4117_, 2);
    lean_inc_ref(v_type_4118_);
    return v_type_4118_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed(
    mut v_ps_4119_: *mut LeanObject,
    mut v_i_4120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4121_: *mut LeanObject = core::ptr::null_mut();
    v_res_4121_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(v_ps_4119_, v_i_4120_);
    lean_dec(v_i_4120_);
    lean_dec_ref(v_ps_4119_);
    return v_res_4121_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(
    mut v_args_4122_: *mut LeanObject,
    mut v_ps_4123_: *mut LeanObject,
    mut v_k_4124_: *mut LeanObject,
    mut v_a_4125_: *mut LeanObject,
    mut v_a_4126_: *mut LeanObject,
    mut v_a_4127_: *mut LeanObject,
    mut v_a_4128_: *mut LeanObject,
    mut v_a_4129_: *mut LeanObject,
    mut v_a_4130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4141_: u8 = 0;
    let mut v___x_4142_: u8 = 0;
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_a_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4132_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_4132_, 0, v_ps_4123_);
                v___x_4133_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_4122_, v___f_4132_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
                if lean_obj_tag(v___x_4133_) == 0 {
                    v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
                    lean_inc(v_a_4134_);
                    lean_dec_ref_known(v___x_4133_, 1);
                    v_fst_4135_ = lean_ctor_get(v_a_4134_, 0);
                    lean_inc(v_fst_4135_);
                    v_snd_4136_ = lean_ctor_get(v_a_4134_, 1);
                    lean_inc(v_snd_4136_);
                    lean_dec(v_a_4134_);
                    lean_inc(v_a_4130_);
                    lean_inc_ref(v_a_4129_);
                    lean_inc(v_a_4128_);
                    lean_inc_ref(v_a_4127_);
                    lean_inc(v_a_4126_);
                    lean_inc_ref(v_a_4125_);
                    v___x_4137_ = lean_apply_8(
                        v_k_4124_,
                        v_fst_4135_,
                        v_a_4125_,
                        v_a_4126_,
                        v_a_4127_,
                        v_a_4128_,
                        v_a_4129_,
                        v_a_4130_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4137_) == 0 {
                        v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
                        v_isSharedCheck_4147_ = (!lean_is_exclusive(v___x_4137_)) as u8;
                        if v_isSharedCheck_4147_ == 0 {
                            v___x_4140_ = v___x_4137_;
                            v_isShared_4141_ = v_isSharedCheck_4147_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4138_);
                            lean_dec(v___x_4137_);
                            v___x_4140_ = lean_box(0);
                            v_isShared_4141_ = v_isSharedCheck_4147_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_4136_);
                        return v___x_4137_;
                    }
                } else {
                    lean_dec_ref(v_k_4124_);
                    v_a_4148_ = lean_ctor_get(v___x_4133_, 0);
                    v_isSharedCheck_4155_ = (!lean_is_exclusive(v___x_4133_)) as u8;
                    if v_isSharedCheck_4155_ == 0 {
                        v___x_4150_ = v___x_4133_;
                        v_isShared_4151_ = v_isSharedCheck_4155_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4148_);
                        lean_dec(v___x_4133_);
                        v___x_4150_ = lean_box(0);
                        v_isShared_4151_ = v_isSharedCheck_4155_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4142_ = 1;
                v___x_4143_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4142_, v_snd_4136_, v_a_4138_);
                lean_dec(v_snd_4136_);
                if v_isShared_4141_ == 0 {
                    lean_ctor_set(v___x_4140_, 0, v___x_4143_);
                    v___x_4145_ = v___x_4140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
                    v___x_4145_ = v_reuseFailAlloc_4146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4145_;
            }
            3 => {
                if v_isShared_4151_ == 0 {
                    v___x_4153_ = v___x_4150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
                    v___x_4153_ = v_reuseFailAlloc_4154_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___boxed(
    mut v_args_4156_: *mut LeanObject,
    mut v_ps_4157_: *mut LeanObject,
    mut v_k_4158_: *mut LeanObject,
    mut v_a_4159_: *mut LeanObject,
    mut v_a_4160_: *mut LeanObject,
    mut v_a_4161_: *mut LeanObject,
    mut v_a_4162_: *mut LeanObject,
    mut v_a_4163_: *mut LeanObject,
    mut v_a_4164_: *mut LeanObject,
    mut v_a_4165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4166_: *mut LeanObject = core::ptr::null_mut();
    v_res_4166_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(
            v_args_4156_,
            v_ps_4157_,
            v_k_4158_,
            v_a_4159_,
            v_a_4160_,
            v_a_4161_,
            v_a_4162_,
            v_a_4163_,
            v_a_4164_,
        );
    lean_dec(v_a_4164_);
    lean_dec_ref(v_a_4163_);
    lean_dec(v_a_4162_);
    lean_dec_ref(v_a_4161_);
    lean_dec(v_a_4160_);
    lean_dec_ref(v_a_4159_);
    lean_dec_ref(v_args_4156_);
    return v_res_4166_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    v___x_4170_ = lean_box(0);
    v___x_4171_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1;
    v___x_4172_ = l_Lean_Expr_const___override(v___x_4171_, v___x_4170_);
    return v___x_4172_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(
    mut v_x_4173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    v___x_4174_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
    return v___x_4174_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed(
    mut v_x_4175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4176_: *mut LeanObject = core::ptr::null_mut();
    v_res_4176_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(v_x_4175_);
    lean_dec(v_x_4175_);
    return v_res_4176_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(
    mut v_args_4178_: *mut LeanObject,
    mut v_k_4179_: *mut LeanObject,
    mut v_a_4180_: *mut LeanObject,
    mut v_a_4181_: *mut LeanObject,
    mut v_a_4182_: *mut LeanObject,
    mut v_a_4183_: *mut LeanObject,
    mut v_a_4184_: *mut LeanObject,
    mut v_a_4185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4196_: u8 = 0;
    let mut v___x_4197_: u8 = 0;
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut v_a_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4187_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0;
                v___x_4188_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_4178_, v___f_4187_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
                if lean_obj_tag(v___x_4188_) == 0 {
                    v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
                    lean_inc(v_a_4189_);
                    lean_dec_ref_known(v___x_4188_, 1);
                    v_fst_4190_ = lean_ctor_get(v_a_4189_, 0);
                    lean_inc(v_fst_4190_);
                    v_snd_4191_ = lean_ctor_get(v_a_4189_, 1);
                    lean_inc(v_snd_4191_);
                    lean_dec(v_a_4189_);
                    lean_inc(v_a_4185_);
                    lean_inc_ref(v_a_4184_);
                    lean_inc(v_a_4183_);
                    lean_inc_ref(v_a_4182_);
                    lean_inc(v_a_4181_);
                    lean_inc_ref(v_a_4180_);
                    v___x_4192_ = lean_apply_8(
                        v_k_4179_,
                        v_fst_4190_,
                        v_a_4180_,
                        v_a_4181_,
                        v_a_4182_,
                        v_a_4183_,
                        v_a_4184_,
                        v_a_4185_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4192_) == 0 {
                        v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
                        v_isSharedCheck_4202_ = (!lean_is_exclusive(v___x_4192_)) as u8;
                        if v_isSharedCheck_4202_ == 0 {
                            v___x_4195_ = v___x_4192_;
                            v_isShared_4196_ = v_isSharedCheck_4202_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4193_);
                            lean_dec(v___x_4192_);
                            v___x_4195_ = lean_box(0);
                            v_isShared_4196_ = v_isSharedCheck_4202_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_4191_);
                        return v___x_4192_;
                    }
                } else {
                    lean_dec_ref(v_k_4179_);
                    v_a_4203_ = lean_ctor_get(v___x_4188_, 0);
                    v_isSharedCheck_4210_ = (!lean_is_exclusive(v___x_4188_)) as u8;
                    if v_isSharedCheck_4210_ == 0 {
                        v___x_4205_ = v___x_4188_;
                        v_isShared_4206_ = v_isSharedCheck_4210_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4203_);
                        lean_dec(v___x_4188_);
                        v___x_4205_ = lean_box(0);
                        v_isShared_4206_ = v_isSharedCheck_4210_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4197_ = 1;
                v___x_4198_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4197_, v_snd_4191_, v_a_4193_);
                lean_dec(v_snd_4191_);
                if v_isShared_4196_ == 0 {
                    lean_ctor_set(v___x_4195_, 0, v___x_4198_);
                    v___x_4200_ = v___x_4195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4198_);
                    v___x_4200_ = v_reuseFailAlloc_4201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4200_;
            }
            3 => {
                if v_isShared_4206_ == 0 {
                    v___x_4208_ = v___x_4205_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
                    v___x_4208_ = v_reuseFailAlloc_4209_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___boxed(
    mut v_args_4211_: *mut LeanObject,
    mut v_k_4212_: *mut LeanObject,
    mut v_a_4213_: *mut LeanObject,
    mut v_a_4214_: *mut LeanObject,
    mut v_a_4215_: *mut LeanObject,
    mut v_a_4216_: *mut LeanObject,
    mut v_a_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v_a_4219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4220_: *mut LeanObject = core::ptr::null_mut();
    v_res_4220_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(
            v_args_4211_,
            v_k_4212_,
            v_a_4213_,
            v_a_4214_,
            v_a_4215_,
            v_a_4216_,
            v_a_4217_,
            v_a_4218_,
        );
    lean_dec(v_a_4218_);
    lean_dec_ref(v_a_4217_);
    lean_dec(v_a_4216_);
    lean_dec_ref(v_a_4215_);
    lean_dec(v_a_4214_);
    lean_dec_ref(v_a_4213_);
    lean_dec_ref(v_args_4211_);
    return v_res_4220_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4221_: u8 = 0;
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    v___x_4221_ = 1;
    v___x_4222_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_4221_);
    return v___x_4222_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(
    mut v_msg_4223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    v___x_4224_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
    v___x_4225_ = lean_panic_fn_borrowed(v___x_4224_, v_msg_4223_);
    return v___x_4225_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    v___x_4229_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2;
    v___x_4230_ = lean_unsigned_to_nat(9);
    v___x_4231_ = lean_unsigned_to_nat(616);
    v___x_4232_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1;
    v___x_4233_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0;
    v___x_4234_ = l_mkPanicMessageWithDecl(
        v___x_4233_,
        v___x_4232_,
        v___x_4231_,
        v___x_4230_,
        v___x_4229_,
    );
    return v___x_4234_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(
    mut v_code_4235_: *mut LeanObject,
    mut v_decl_4236_: *mut LeanObject,
    mut v_k_4237_: *mut LeanObject,
    mut v_a_4238_: *mut LeanObject,
    mut v_a_4239_: *mut LeanObject,
    mut v_a_4240_: *mut LeanObject,
    mut v_a_4241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4244_: u8 = 0;
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: u8 = 0;
    let mut v_decl_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: usize = 0;
    let mut v___x_4254_: usize = 0;
    let mut v___x_4255_: u8 = 0;
    let mut v___x_4256_: usize = 0;
    let mut v___x_4257_: usize = 0;
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: u8 = 0;
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4273_: u8 = 0;
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4279_: u8 = 0;
    let mut v_a_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4283_: u8 = 0;
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut v_a_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4291_: u8 = 0;
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_4248_ = lean_ctor_get(v_decl_4236_, 2);
                v_value_4249_ = lean_ctor_get(v_decl_4236_, 3);
                v___x_4250_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_4248_);
                if v___x_4250_ == 0 {
                    if lean_obj_tag(v_code_4235_) == 0 {
                        v_decl_4251_ = lean_ctor_get(v_code_4235_, 0);
                        v_k_4252_ = lean_ctor_get(v_code_4235_, 1);
                        v___x_4253_ = lean_ptr_addr(v_k_4252_);
                        v___x_4254_ = lean_ptr_addr(v_k_4237_);
                        v___x_4255_ = lean_usize_dec_eq(v___x_4253_, v___x_4254_);
                        if v___x_4255_ == 0 {
                            v___y_4244_ = v___x_4255_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4256_ = lean_ptr_addr(v_decl_4251_);
                            v___x_4257_ = lean_ptr_addr(v_decl_4236_);
                            v___x_4258_ = lean_usize_dec_eq(v___x_4256_, v___x_4257_);
                            v___y_4244_ = v___x_4258_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_k_4237_);
                        lean_dec_ref(v_decl_4236_);
                        lean_dec_ref(v_code_4235_);
                        v___x_4259_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
                        v___x_4260_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_4259_);
                        v___x_4261_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4261_, 0, v___x_4260_);
                        return v___x_4261_;
                    }
                } else {
                    lean_dec_ref(v_code_4235_);
                    v___x_4262_ = 1;
                    v___x_4263_ = lean_box(0);
                    v___x_4264_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
                    lean_inc(v_value_4249_);
                    v___x_4265_ = l_Lean_Compiler_LCNF_mkLetDecl(
                        v___x_4262_,
                        v___x_4263_,
                        v___x_4264_,
                        v_value_4249_,
                        v_a_4238_,
                        v_a_4239_,
                        v_a_4240_,
                        v_a_4241_,
                    );
                    if lean_obj_tag(v___x_4265_) == 0 {
                        v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
                        lean_inc(v_a_4266_);
                        lean_dec_ref_known(v___x_4265_, 1);
                        v_fvarId_4267_ = lean_ctor_get(v_a_4266_, 0);
                        lean_inc(v_fvarId_4267_);
                        v___x_4268_ = lean_alloc_ctor(14, 1, (0) as u32);
                        lean_ctor_set(v___x_4268_, 0, v_fvarId_4267_);
                        v___x_4269_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                            v___x_4262_,
                            v_decl_4236_,
                            v___x_4268_,
                            v_a_4239_,
                        );
                        if lean_obj_tag(v___x_4269_) == 0 {
                            v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
                            v_isSharedCheck_4279_ = (!lean_is_exclusive(v___x_4269_)) as u8;
                            if v_isSharedCheck_4279_ == 0 {
                                v___x_4272_ = v___x_4269_;
                                v_isShared_4273_ = v_isSharedCheck_4279_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_4270_);
                                lean_dec(v___x_4269_);
                                v___x_4272_ = lean_box(0);
                                v_isShared_4273_ = v_isSharedCheck_4279_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4266_);
                            lean_dec_ref(v_k_4237_);
                            v_a_4280_ = lean_ctor_get(v___x_4269_, 0);
                            v_isSharedCheck_4287_ = (!lean_is_exclusive(v___x_4269_)) as u8;
                            if v_isSharedCheck_4287_ == 0 {
                                v___x_4282_ = v___x_4269_;
                                v_isShared_4283_ = v_isSharedCheck_4287_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4280_);
                                lean_dec(v___x_4269_);
                                v___x_4282_ = lean_box(0);
                                v_isShared_4283_ = v_isSharedCheck_4287_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_k_4237_);
                        lean_dec_ref(v_decl_4236_);
                        v_a_4288_ = lean_ctor_get(v___x_4265_, 0);
                        v_isSharedCheck_4295_ = (!lean_is_exclusive(v___x_4265_)) as u8;
                        if v_isSharedCheck_4295_ == 0 {
                            v___x_4290_ = v___x_4265_;
                            v_isShared_4291_ = v_isSharedCheck_4295_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4288_);
                            lean_dec(v___x_4265_);
                            v___x_4290_ = lean_box(0);
                            v_isShared_4291_ = v_isSharedCheck_4295_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_4244_ == 0 {
                    lean_dec_ref(v_code_4235_);
                    v___x_4245_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4245_, 0, v_decl_4236_);
                    lean_ctor_set(v___x_4245_, 1, v_k_4237_);
                    v___x_4246_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4246_, 0, v___x_4245_);
                    return v___x_4246_;
                } else {
                    lean_dec_ref(v_k_4237_);
                    lean_dec_ref(v_decl_4236_);
                    v___x_4247_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4247_, 0, v_code_4235_);
                    return v___x_4247_;
                }
            }
            2 => {
                v___x_4274_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4274_, 0, v_a_4270_);
                lean_ctor_set(v___x_4274_, 1, v_k_4237_);
                v___x_4275_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4275_, 0, v_a_4266_);
                lean_ctor_set(v___x_4275_, 1, v___x_4274_);
                if v_isShared_4273_ == 0 {
                    lean_ctor_set(v___x_4272_, 0, v___x_4275_);
                    v___x_4277_ = v___x_4272_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
                    v___x_4277_ = v_reuseFailAlloc_4278_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4277_;
            }
            4 => {
                if v_isShared_4283_ == 0 {
                    v___x_4285_ = v___x_4282_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
                    v___x_4285_ = v_reuseFailAlloc_4286_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4285_;
            }
            6 => {
                if v_isShared_4291_ == 0 {
                    v___x_4293_ = v___x_4290_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
                    v___x_4293_ = v_reuseFailAlloc_4294_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___boxed(
    mut v_code_4296_: *mut LeanObject,
    mut v_decl_4297_: *mut LeanObject,
    mut v_k_4298_: *mut LeanObject,
    mut v_a_4299_: *mut LeanObject,
    mut v_a_4300_: *mut LeanObject,
    mut v_a_4301_: *mut LeanObject,
    mut v_a_4302_: *mut LeanObject,
    mut v_a_4303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4304_: *mut LeanObject = core::ptr::null_mut();
    v_res_4304_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_4296_, v_decl_4297_, v_k_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_);
    lean_dec(v_a_4302_);
    lean_dec_ref(v_a_4301_);
    lean_dec(v_a_4300_);
    lean_dec_ref(v_a_4299_);
    return v_res_4304_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(
    mut v_code_4305_: *mut LeanObject,
    mut v_decl_4306_: *mut LeanObject,
    mut v_k_4307_: *mut LeanObject,
    mut v_a_4308_: *mut LeanObject,
    mut v_a_4309_: *mut LeanObject,
    mut v_a_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
    mut v_a_4312_: *mut LeanObject,
    mut v_a_4313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    v___x_4315_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_4305_, v_decl_4306_, v_k_4307_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
    return v___x_4315_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___boxed(
    mut v_code_4316_: *mut LeanObject,
    mut v_decl_4317_: *mut LeanObject,
    mut v_k_4318_: *mut LeanObject,
    mut v_a_4319_: *mut LeanObject,
    mut v_a_4320_: *mut LeanObject,
    mut v_a_4321_: *mut LeanObject,
    mut v_a_4322_: *mut LeanObject,
    mut v_a_4323_: *mut LeanObject,
    mut v_a_4324_: *mut LeanObject,
    mut v_a_4325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4326_: *mut LeanObject = core::ptr::null_mut();
    v_res_4326_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(
            v_code_4316_,
            v_decl_4317_,
            v_k_4318_,
            v_a_4319_,
            v_a_4320_,
            v_a_4321_,
            v_a_4322_,
            v_a_4323_,
            v_a_4324_,
        );
    lean_dec(v_a_4324_);
    lean_dec_ref(v_a_4323_);
    lean_dec(v_a_4322_);
    lean_dec_ref(v_a_4321_);
    lean_dec(v_a_4320_);
    lean_dec_ref(v_a_4319_);
    return v_res_4326_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(
    mut v_code_4327_: *mut LeanObject,
    mut v_decl_4328_: *mut LeanObject,
    mut v_expType_4329_: *mut LeanObject,
    mut v_k_4330_: *mut LeanObject,
    mut v_a_4331_: *mut LeanObject,
    mut v_a_4332_: *mut LeanObject,
    mut v_a_4333_: *mut LeanObject,
    mut v_a_4334_: *mut LeanObject,
    mut v_a_4335_: *mut LeanObject,
    mut v_a_4336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4339_: u8 = 0;
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: u8 = 0;
    let mut v_boxedTy_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: u8 = 0;
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4365_: u8 = 0;
    let mut v_a_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4369_: u8 = 0;
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4373_: u8 = 0;
    let mut v_a_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4381_: u8 = 0;
    let mut v_a_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4385_: u8 = 0;
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut v_decl_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: usize = 0;
    let mut v___x_4393_: usize = 0;
    let mut v___x_4394_: u8 = 0;
    let mut v___x_4395_: usize = 0;
    let mut v___x_4396_: usize = 0;
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_4343_ = lean_ctor_get(v_decl_4328_, 2);
                v_value_4344_ = lean_ctor_get(v_decl_4328_, 3);
                v___x_4345_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_type_4343_, v_expType_4329_);
                if v___x_4345_ == 0 {
                    lean_dec_ref(v_code_4327_);
                    v_boxedTy_4346_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_4343_);
                    v___x_4347_ = 1;
                    v___x_4348_ = lean_box(0);
                    lean_inc(v_value_4344_);
                    v___x_4349_ = l_Lean_Compiler_LCNF_mkLetDecl(
                        v___x_4347_,
                        v___x_4348_,
                        v_boxedTy_4346_,
                        v_value_4344_,
                        v_a_4333_,
                        v_a_4334_,
                        v_a_4335_,
                        v_a_4336_,
                    );
                    if lean_obj_tag(v___x_4349_) == 0 {
                        v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
                        lean_inc(v_a_4350_);
                        lean_dec_ref_known(v___x_4349_, 1);
                        v_fvarId_4351_ = lean_ctor_get(v_a_4350_, 0);
                        v_type_4352_ = lean_ctor_get(v_a_4350_, 2);
                        lean_inc_ref(v_type_4343_);
                        lean_inc_ref(v_type_4352_);
                        lean_inc(v_fvarId_4351_);
                        v___x_4353_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_4351_, v_type_4352_, v_type_4343_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
                        if lean_obj_tag(v___x_4353_) == 0 {
                            v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
                            lean_inc(v_a_4354_);
                            lean_dec_ref_known(v___x_4353_, 1);
                            v___x_4355_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                                v___x_4347_,
                                v_decl_4328_,
                                v_a_4354_,
                                v_a_4334_,
                            );
                            if lean_obj_tag(v___x_4355_) == 0 {
                                v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
                                v_isSharedCheck_4365_ = (!lean_is_exclusive(v___x_4355_)) as u8;
                                if v_isSharedCheck_4365_ == 0 {
                                    v___x_4358_ = v___x_4355_;
                                    v_isShared_4359_ = v_isSharedCheck_4365_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_4356_);
                                    lean_dec(v___x_4355_);
                                    v___x_4358_ = lean_box(0);
                                    v_isShared_4359_ = v_isSharedCheck_4365_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4350_);
                                lean_dec_ref(v_k_4330_);
                                v_a_4366_ = lean_ctor_get(v___x_4355_, 0);
                                v_isSharedCheck_4373_ = (!lean_is_exclusive(v___x_4355_)) as u8;
                                if v_isSharedCheck_4373_ == 0 {
                                    v___x_4368_ = v___x_4355_;
                                    v_isShared_4369_ = v_isSharedCheck_4373_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4366_);
                                    lean_dec(v___x_4355_);
                                    v___x_4368_ = lean_box(0);
                                    v_isShared_4369_ = v_isSharedCheck_4373_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4350_);
                            lean_dec_ref(v_k_4330_);
                            lean_dec_ref(v_decl_4328_);
                            v_a_4374_ = lean_ctor_get(v___x_4353_, 0);
                            v_isSharedCheck_4381_ = (!lean_is_exclusive(v___x_4353_)) as u8;
                            if v_isSharedCheck_4381_ == 0 {
                                v___x_4376_ = v___x_4353_;
                                v_isShared_4377_ = v_isSharedCheck_4381_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_4374_);
                                lean_dec(v___x_4353_);
                                v___x_4376_ = lean_box(0);
                                v_isShared_4377_ = v_isSharedCheck_4381_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_k_4330_);
                        lean_dec_ref(v_decl_4328_);
                        v_a_4382_ = lean_ctor_get(v___x_4349_, 0);
                        v_isSharedCheck_4389_ = (!lean_is_exclusive(v___x_4349_)) as u8;
                        if v_isSharedCheck_4389_ == 0 {
                            v___x_4384_ = v___x_4349_;
                            v_isShared_4385_ = v_isSharedCheck_4389_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4382_);
                            lean_dec(v___x_4349_);
                            v___x_4384_ = lean_box(0);
                            v_isShared_4385_ = v_isSharedCheck_4389_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_code_4327_) == 0 {
                        v_decl_4390_ = lean_ctor_get(v_code_4327_, 0);
                        v_k_4391_ = lean_ctor_get(v_code_4327_, 1);
                        v___x_4392_ = lean_ptr_addr(v_k_4391_);
                        v___x_4393_ = lean_ptr_addr(v_k_4330_);
                        v___x_4394_ = lean_usize_dec_eq(v___x_4392_, v___x_4393_);
                        if v___x_4394_ == 0 {
                            v___y_4339_ = v___x_4394_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4395_ = lean_ptr_addr(v_decl_4390_);
                            v___x_4396_ = lean_ptr_addr(v_decl_4328_);
                            v___x_4397_ = lean_usize_dec_eq(v___x_4395_, v___x_4396_);
                            v___y_4339_ = v___x_4397_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_k_4330_);
                        lean_dec_ref(v_decl_4328_);
                        lean_dec_ref(v_code_4327_);
                        v___x_4398_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
                        v___x_4399_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_4398_);
                        v___x_4400_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4400_, 0, v___x_4399_);
                        return v___x_4400_;
                    }
                }
            }
            1 => {
                if v___y_4339_ == 0 {
                    lean_dec_ref(v_code_4327_);
                    v___x_4340_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4340_, 0, v_decl_4328_);
                    lean_ctor_set(v___x_4340_, 1, v_k_4330_);
                    v___x_4341_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4341_, 0, v___x_4340_);
                    return v___x_4341_;
                } else {
                    lean_dec_ref(v_k_4330_);
                    lean_dec_ref(v_decl_4328_);
                    v___x_4342_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4342_, 0, v_code_4327_);
                    return v___x_4342_;
                }
            }
            2 => {
                v___x_4360_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4360_, 0, v_a_4356_);
                lean_ctor_set(v___x_4360_, 1, v_k_4330_);
                v___x_4361_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4361_, 0, v_a_4350_);
                lean_ctor_set(v___x_4361_, 1, v___x_4360_);
                if v_isShared_4359_ == 0 {
                    lean_ctor_set(v___x_4358_, 0, v___x_4361_);
                    v___x_4363_ = v___x_4358_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4361_);
                    v___x_4363_ = v_reuseFailAlloc_4364_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4363_;
            }
            4 => {
                if v_isShared_4369_ == 0 {
                    v___x_4371_ = v___x_4368_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
                    v___x_4371_ = v_reuseFailAlloc_4372_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4371_;
            }
            6 => {
                if v_isShared_4377_ == 0 {
                    v___x_4379_ = v___x_4376_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
                    v___x_4379_ = v_reuseFailAlloc_4380_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4379_;
            }
            8 => {
                if v_isShared_4385_ == 0 {
                    v___x_4387_ = v___x_4384_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
                    v___x_4387_ = v_reuseFailAlloc_4388_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded___boxed(
    mut v_code_4401_: *mut LeanObject,
    mut v_decl_4402_: *mut LeanObject,
    mut v_expType_4403_: *mut LeanObject,
    mut v_k_4404_: *mut LeanObject,
    mut v_a_4405_: *mut LeanObject,
    mut v_a_4406_: *mut LeanObject,
    mut v_a_4407_: *mut LeanObject,
    mut v_a_4408_: *mut LeanObject,
    mut v_a_4409_: *mut LeanObject,
    mut v_a_4410_: *mut LeanObject,
    mut v_a_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4412_: *mut LeanObject = core::ptr::null_mut();
    v_res_4412_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(
            v_code_4401_,
            v_decl_4402_,
            v_expType_4403_,
            v_k_4404_,
            v_a_4405_,
            v_a_4406_,
            v_a_4407_,
            v_a_4408_,
            v_a_4409_,
            v_a_4410_,
        );
    lean_dec(v_a_4410_);
    lean_dec_ref(v_a_4409_);
    lean_dec(v_a_4408_);
    lean_dec_ref(v_a_4407_);
    lean_dec(v_a_4406_);
    lean_dec_ref(v_a_4405_);
    lean_dec_ref(v_expType_4403_);
    return v_res_4412_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    v___x_4413_ = l_instMonadEIO(lean_box(0));
    return v___x_4413_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(
    mut v_msg_4418_: *mut LeanObject,
    mut v___y_4419_: *mut LeanObject,
    mut v___y_4420_: *mut LeanObject,
    mut v___y_4421_: *mut LeanObject,
    mut v___y_4422_: *mut LeanObject,
    mut v___y_4423_: *mut LeanObject,
    mut v___y_4424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v_toFunctor_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4438_: u8 = 0;
    let mut v___f_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4455_: u8 = 0;
    let mut v_toFunctor_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___f_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273__overap_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut v_unused_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_unused_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4489_: u8 = 0;
    let mut v_unused_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4491_: u8 = 0;
    let mut v_unused_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4426_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
                v___x_4427_ = l_StateRefT_x27_instMonad___redArg(v___x_4426_);
                v_toApplicative_4428_ = lean_ctor_get(v___x_4427_, 0);
                v_isSharedCheck_4491_ = (!lean_is_exclusive(v___x_4427_)) as u8;
                if v_isSharedCheck_4491_ == 0 {
                    v_unused_4492_ = lean_ctor_get(v___x_4427_, 1);
                    lean_dec(v_unused_4492_);
                    v___x_4430_ = v___x_4427_;
                    v_isShared_4431_ = v_isSharedCheck_4491_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4428_);
                    lean_dec(v___x_4427_);
                    v___x_4430_ = lean_box(0);
                    v_isShared_4431_ = v_isSharedCheck_4491_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4432_ = lean_ctor_get(v_toApplicative_4428_, 0);
                v_toSeq_4433_ = lean_ctor_get(v_toApplicative_4428_, 2);
                v_toSeqLeft_4434_ = lean_ctor_get(v_toApplicative_4428_, 3);
                v_toSeqRight_4435_ = lean_ctor_get(v_toApplicative_4428_, 4);
                v_isSharedCheck_4489_ = (!lean_is_exclusive(v_toApplicative_4428_)) as u8;
                if v_isSharedCheck_4489_ == 0 {
                    v_unused_4490_ = lean_ctor_get(v_toApplicative_4428_, 1);
                    lean_dec(v_unused_4490_);
                    v___x_4437_ = v_toApplicative_4428_;
                    v_isShared_4438_ = v_isSharedCheck_4489_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4435_);
                    lean_inc(v_toSeqLeft_4434_);
                    lean_inc(v_toSeq_4433_);
                    lean_inc(v_toFunctor_4432_);
                    lean_dec(v_toApplicative_4428_);
                    v___x_4437_ = lean_box(0);
                    v_isShared_4438_ = v_isSharedCheck_4489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4439_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1;
                v___f_4440_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_4432_);
                v___f_4441_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4441_, 0, v_toFunctor_4432_);
                v___f_4442_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4442_, 0, v_toFunctor_4432_);
                v___x_4443_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4443_, 0, v___f_4441_);
                lean_ctor_set(v___x_4443_, 1, v___f_4442_);
                v___f_4444_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4444_, 0, v_toSeqRight_4435_);
                v___f_4445_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4445_, 0, v_toSeqLeft_4434_);
                v___f_4446_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4446_, 0, v_toSeq_4433_);
                if v_isShared_4438_ == 0 {
                    lean_ctor_set(v___x_4437_, 4, v___f_4444_);
                    lean_ctor_set(v___x_4437_, 3, v___f_4445_);
                    lean_ctor_set(v___x_4437_, 2, v___f_4446_);
                    lean_ctor_set(v___x_4437_, 1, v___f_4439_);
                    lean_ctor_set(v___x_4437_, 0, v___x_4443_);
                    v___x_4448_ = v___x_4437_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4443_);
                    lean_ctor_set(v_reuseFailAlloc_4488_, 1, v___f_4439_);
                    lean_ctor_set(v_reuseFailAlloc_4488_, 2, v___f_4446_);
                    lean_ctor_set(v_reuseFailAlloc_4488_, 3, v___f_4445_);
                    lean_ctor_set(v_reuseFailAlloc_4488_, 4, v___f_4444_);
                    v___x_4448_ = v_reuseFailAlloc_4488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4431_ == 0 {
                    lean_ctor_set(v___x_4430_, 1, v___f_4440_);
                    lean_ctor_set(v___x_4430_, 0, v___x_4448_);
                    v___x_4450_ = v___x_4430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4448_);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 1, v___f_4440_);
                    v___x_4450_ = v_reuseFailAlloc_4487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4451_ = l_StateRefT_x27_instMonad___redArg(v___x_4450_);
                v_toApplicative_4452_ = lean_ctor_get(v___x_4451_, 0);
                v_isSharedCheck_4485_ = (!lean_is_exclusive(v___x_4451_)) as u8;
                if v_isSharedCheck_4485_ == 0 {
                    v_unused_4486_ = lean_ctor_get(v___x_4451_, 1);
                    lean_dec(v_unused_4486_);
                    v___x_4454_ = v___x_4451_;
                    v_isShared_4455_ = v_isSharedCheck_4485_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4452_);
                    lean_dec(v___x_4451_);
                    v___x_4454_ = lean_box(0);
                    v_isShared_4455_ = v_isSharedCheck_4485_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4456_ = lean_ctor_get(v_toApplicative_4452_, 0);
                v_toSeq_4457_ = lean_ctor_get(v_toApplicative_4452_, 2);
                v_toSeqLeft_4458_ = lean_ctor_get(v_toApplicative_4452_, 3);
                v_toSeqRight_4459_ = lean_ctor_get(v_toApplicative_4452_, 4);
                v_isSharedCheck_4483_ = (!lean_is_exclusive(v_toApplicative_4452_)) as u8;
                if v_isSharedCheck_4483_ == 0 {
                    v_unused_4484_ = lean_ctor_get(v_toApplicative_4452_, 1);
                    lean_dec(v_unused_4484_);
                    v___x_4461_ = v_toApplicative_4452_;
                    v_isShared_4462_ = v_isSharedCheck_4483_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4459_);
                    lean_inc(v_toSeqLeft_4458_);
                    lean_inc(v_toSeq_4457_);
                    lean_inc(v_toFunctor_4456_);
                    lean_dec(v_toApplicative_4452_);
                    v___x_4461_ = lean_box(0);
                    v_isShared_4462_ = v_isSharedCheck_4483_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4463_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3;
                v___f_4464_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4;
                lean_inc_ref(v_toFunctor_4456_);
                v___f_4465_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4465_, 0, v_toFunctor_4456_);
                v___f_4466_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4466_, 0, v_toFunctor_4456_);
                v___x_4467_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4467_, 0, v___f_4465_);
                lean_ctor_set(v___x_4467_, 1, v___f_4466_);
                v___f_4468_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4468_, 0, v_toSeqRight_4459_);
                v___f_4469_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4469_, 0, v_toSeqLeft_4458_);
                v___f_4470_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4470_, 0, v_toSeq_4457_);
                if v_isShared_4462_ == 0 {
                    lean_ctor_set(v___x_4461_, 4, v___f_4468_);
                    lean_ctor_set(v___x_4461_, 3, v___f_4469_);
                    lean_ctor_set(v___x_4461_, 2, v___f_4470_);
                    lean_ctor_set(v___x_4461_, 1, v___f_4463_);
                    lean_ctor_set(v___x_4461_, 0, v___x_4467_);
                    v___x_4472_ = v___x_4461_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4467_);
                    lean_ctor_set(v_reuseFailAlloc_4482_, 1, v___f_4463_);
                    lean_ctor_set(v_reuseFailAlloc_4482_, 2, v___f_4470_);
                    lean_ctor_set(v_reuseFailAlloc_4482_, 3, v___f_4469_);
                    lean_ctor_set(v_reuseFailAlloc_4482_, 4, v___f_4468_);
                    v___x_4472_ = v_reuseFailAlloc_4482_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4455_ == 0 {
                    lean_ctor_set(v___x_4454_, 1, v___f_4464_);
                    lean_ctor_set(v___x_4454_, 0, v___x_4472_);
                    v___x_4474_ = v___x_4454_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4472_);
                    lean_ctor_set(v_reuseFailAlloc_4481_, 1, v___f_4464_);
                    v___x_4474_ = v_reuseFailAlloc_4481_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4475_ = l_StateRefT_x27_instMonad___redArg(v___x_4474_);
                v___x_4476_ = l_Lean_instInhabitedExpr;
                v___x_4477_ = l_instInhabitedOfMonad___redArg(v___x_4475_, v___x_4476_);
                v___f_4478_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_4478_, 0, v___x_4477_);
                v___x_3273__overap_4479_ = lean_panic_fn_borrowed(v___f_4478_, v_msg_4418_);
                lean_dec_ref(v___f_4478_);
                lean_inc(v___y_4424_);
                lean_inc_ref(v___y_4423_);
                lean_inc(v___y_4422_);
                lean_inc_ref(v___y_4421_);
                lean_inc(v___y_4420_);
                lean_inc_ref(v___y_4419_);
                v___x_4480_ = lean_apply_7(
                    v___x_3273__overap_4479_,
                    v___y_4419_,
                    v___y_4420_,
                    v___y_4421_,
                    v___y_4422_,
                    v___y_4423_,
                    v___y_4424_,
                    lean_box(0),
                );
                return v___x_4480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___boxed(
    mut v_msg_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
    mut v___y_4500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4501_: *mut LeanObject = core::ptr::null_mut();
    v_res_4501_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v_msg_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
    lean_dec(v___y_4499_);
    lean_dec_ref(v___y_4498_);
    lean_dec(v___y_4497_);
    lean_dec_ref(v___y_4496_);
    lean_dec(v___y_4495_);
    lean_dec_ref(v___y_4494_);
    return v_res_4501_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2()
-> *mut LeanObject {
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    v___x_4504_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2;
    v___x_4505_ = lean_unsigned_to_nat(44);
    v___x_4506_ = lean_unsigned_to_nat(316);
    v___x_4507_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1;
    v___x_4508_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0;
    v___x_4509_ = l_mkPanicMessageWithDecl(
        v___x_4508_,
        v___x_4507_,
        v___x_4506_,
        v___x_4505_,
        v___x_4504_,
    );
    return v___x_4509_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5()
-> *mut LeanObject {
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    v___x_4513_ = lean_box(0);
    v___x_4514_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4;
    v___x_4515_ = l_Lean_Expr_const___override(v___x_4514_, v___x_4513_);
    return v___x_4515_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8()
-> *mut LeanObject {
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    v___x_4519_ = lean_box(0);
    v___x_4520_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7;
    v___x_4521_ = l_Lean_Expr_const___override(v___x_4520_, v___x_4519_);
    return v___x_4521_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11()
-> *mut LeanObject {
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    v___x_4525_ = lean_box(0);
    v___x_4526_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10;
    v___x_4527_ = l_Lean_Expr_const___override(v___x_4526_, v___x_4525_);
    return v___x_4527_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12()
-> *mut LeanObject {
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    v___x_4528_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2;
    v___x_4529_ = lean_unsigned_to_nat(45);
    v___x_4530_ = lean_unsigned_to_nat(301);
    v___x_4531_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1;
    v___x_4532_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0;
    v___x_4533_ = l_mkPanicMessageWithDecl(
        v___x_4532_,
        v___x_4531_,
        v___x_4530_,
        v___x_4529_,
        v___x_4528_,
    );
    return v___x_4533_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(
    mut v_currentType_4534_: *mut LeanObject,
    mut v_value_4535_: *mut LeanObject,
    mut v_a_4536_: *mut LeanObject,
    mut v_a_4537_: *mut LeanObject,
    mut v_a_4538_: *mut LeanObject,
    mut v_a_4539_: *mut LeanObject,
    mut v_a_4540_: *mut LeanObject,
    mut v_a_4541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v_val_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4559_: u8 = 0;
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: u8 = 0;
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4569_: u8 = 0;
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4572_: u8 = 0;
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4577_: u8 = 0;
    let mut v_unused_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4582_: u8 = 0;
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4595_: u8 = 0;
    let mut v_val_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut v_a_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4607_: u8 = 0;
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4611_: u8 = 0;
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_value_4535_) {
                0 => {
                    v_value_4552_ = lean_ctor_get(v_value_4535_, 0);
                    v_isSharedCheck_4582_ = (!lean_is_exclusive(v_value_4535_)) as u8;
                    if v_isSharedCheck_4582_ == 0 {
                        v___x_4554_ = v_value_4535_;
                        v_isShared_4555_ = v_isSharedCheck_4582_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_value_4552_);
                        lean_dec(v_value_4535_);
                        v___x_4554_ = lean_box(0);
                        v_isShared_4555_ = v_isSharedCheck_4582_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    lean_dec_ref(v_currentType_4534_);
                    v___x_4583_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
                    v___x_4584_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4584_, 0, v___x_4583_);
                    return v___x_4584_;
                }
                5 => {
                    lean_dec_ref(v_currentType_4534_);
                    v_i_4585_ = lean_ctor_get(v_value_4535_, 0);
                    lean_inc_ref(v_i_4585_);
                    lean_dec_ref_known(v_value_4535_, 2);
                    v___x_4586_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_i_4585_);
                    lean_dec_ref(v_i_4585_);
                    v___x_4587_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4587_, 0, v___x_4586_);
                    return v___x_4587_;
                }
                7 => {
                    lean_dec_ref_known(v_value_4535_, 2);
                    lean_dec_ref(v_currentType_4534_);
                    v___x_4588_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
                    v___x_4589_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4589_, 0, v___x_4588_);
                    return v___x_4589_;
                }
                9 => {
                    lean_dec_ref(v_currentType_4534_);
                    v_fn_4590_ = lean_ctor_get(v_value_4535_, 0);
                    lean_inc(v_fn_4590_);
                    lean_dec_ref_known(v_value_4535_, 2);
                    v___x_4591_ =
                        l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_4590_, v_a_4541_);
                    if lean_obj_tag(v___x_4591_) == 0 {
                        v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
                        v_isSharedCheck_4603_ = (!lean_is_exclusive(v___x_4591_)) as u8;
                        if v_isSharedCheck_4603_ == 0 {
                            v___x_4594_ = v___x_4591_;
                            v_isShared_4595_ = v_isSharedCheck_4603_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_4592_);
                            lean_dec(v___x_4591_);
                            v___x_4594_ = lean_box(0);
                            v_isShared_4595_ = v_isSharedCheck_4603_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_4604_ = lean_ctor_get(v___x_4591_, 0);
                        v_isSharedCheck_4611_ = (!lean_is_exclusive(v___x_4591_)) as u8;
                        if v_isSharedCheck_4611_ == 0 {
                            v___x_4606_ = v___x_4591_;
                            v_isShared_4607_ = v_isSharedCheck_4611_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4604_);
                            lean_dec(v___x_4591_);
                            v___x_4606_ = lean_box(0);
                            v_isShared_4607_ = v_isSharedCheck_4611_;
                            state = 11;
                            continue;
                        }
                    }
                }
                10 => {
                    lean_dec_ref_known(v_value_4535_, 2);
                    lean_dec_ref(v_currentType_4534_);
                    v___x_4612_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
                    v___x_4613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4613_, 0, v___x_4612_);
                    return v___x_4613_;
                }
                13 => {
                    lean_dec_ref_known(v_value_4535_, 2);
                    lean_dec_ref(v_currentType_4534_);
                    v___x_4614_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
                    v___x_4615_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_4614_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
                    return v___x_4615_;
                }
                14 => {
                    lean_dec_ref_known(v_value_4535_, 1);
                    lean_dec_ref(v_currentType_4534_);
                    v___y_4544_ = v_a_4536_;
                    v___y_4545_ = v_a_4537_;
                    v___y_4546_ = v_a_4538_;
                    v___y_4547_ = v_a_4539_;
                    v___y_4548_ = v_a_4540_;
                    v___y_4549_ = v_a_4541_;
                    state = 1;
                    continue;
                }
                15 => {
                    lean_dec_ref_known(v_value_4535_, 1);
                    lean_dec_ref(v_currentType_4534_);
                    v___y_4544_ = v_a_4536_;
                    v___y_4545_ = v_a_4537_;
                    v___y_4546_ = v_a_4538_;
                    v___y_4547_ = v_a_4539_;
                    v___y_4548_ = v_a_4540_;
                    v___y_4549_ = v_a_4541_;
                    state = 1;
                    continue;
                }
                _ => {
                    lean_dec(v_value_4535_);
                    v___x_4616_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4616_, 0, v_currentType_4534_);
                    return v___x_4616_;
                }
            },
            1 => {
                v___x_4550_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
                v___x_4551_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_4550_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
                return v___x_4551_;
            }
            2 => match lean_obj_tag(v_value_4552_) {
                0 => {
                    lean_del_object(v___x_4554_);
                    v_val_4556_ = lean_ctor_get(v_value_4552_, 0);
                    v_isSharedCheck_4569_ = (!lean_is_exclusive(v_value_4552_)) as u8;
                    if v_isSharedCheck_4569_ == 0 {
                        v___x_4558_ = v_value_4552_;
                        v_isShared_4559_ = v_isSharedCheck_4569_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_4556_);
                        lean_dec(v_value_4552_);
                        v___x_4558_ = lean_box(0);
                        v_isShared_4559_ = v_isSharedCheck_4569_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_4554_);
                    lean_dec_ref(v_currentType_4534_);
                    v_isSharedCheck_4577_ = (!lean_is_exclusive(v_value_4552_)) as u8;
                    if v_isSharedCheck_4577_ == 0 {
                        v_unused_4578_ = lean_ctor_get(v_value_4552_, 0);
                        lean_dec(v_unused_4578_);
                        v___x_4571_ = v_value_4552_;
                        v_isShared_4572_ = v_isSharedCheck_4577_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_value_4552_);
                        v___x_4571_ = lean_box(0);
                        v_isShared_4572_ = v_isSharedCheck_4577_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_value_4552_);
                    if v_isShared_4555_ == 0 {
                        lean_ctor_set(v___x_4554_, 0, v_currentType_4534_);
                        v___x_4580_ = v___x_4554_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_currentType_4534_);
                        v___x_4580_ = v_reuseFailAlloc_4581_;
                        state = 8;
                        continue;
                    }
                }
            },
            3 => {
                v___x_4560_ = l_Lean_maxSmallNat;
                v___x_4561_ = lean_nat_dec_le(v_val_4556_, v___x_4560_);
                lean_dec(v_val_4556_);
                if v___x_4561_ == 0 {
                    if v_isShared_4559_ == 0 {
                        lean_ctor_set(v___x_4558_, 0, v_currentType_4534_);
                        v___x_4563_ = v___x_4558_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_currentType_4534_);
                        v___x_4563_ = v_reuseFailAlloc_4564_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_currentType_4534_);
                    v___x_4565_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
                    if v_isShared_4559_ == 0 {
                        lean_ctor_set(v___x_4558_, 0, v___x_4565_);
                        v___x_4567_ = v___x_4558_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
                        v___x_4567_ = v_reuseFailAlloc_4568_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4563_;
            }
            5 => {
                return v___x_4567_;
            }
            6 => {
                v___x_4573_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
                if v_isShared_4572_ == 0 {
                    lean_ctor_set_tag(v___x_4571_, 0);
                    lean_ctor_set(v___x_4571_, 0, v___x_4573_);
                    v___x_4575_ = v___x_4571_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4573_);
                    v___x_4575_ = v_reuseFailAlloc_4576_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4575_;
            }
            8 => {
                return v___x_4580_;
            }
            9 => {
                if lean_obj_tag(v_a_4592_) == 1 {
                    v_val_4596_ = lean_ctor_get(v_a_4592_, 0);
                    lean_inc(v_val_4596_);
                    lean_dec_ref_known(v_a_4592_, 1);
                    v_type_4597_ = lean_ctor_get(v_val_4596_, 2);
                    lean_inc_ref(v_type_4597_);
                    lean_dec(v_val_4596_);
                    if v_isShared_4595_ == 0 {
                        lean_ctor_set(v___x_4594_, 0, v_type_4597_);
                        v___x_4599_ = v___x_4594_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_type_4597_);
                        v___x_4599_ = v_reuseFailAlloc_4600_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4594_);
                    lean_dec(v_a_4592_);
                    v___x_4601_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
                    v___x_4602_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_4601_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
                    return v___x_4602_;
                }
            }
            10 => {
                return v___x_4599_;
            }
            11 => {
                if v_isShared_4607_ == 0 {
                    v___x_4609_ = v___x_4606_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
                    v___x_4609_ = v_reuseFailAlloc_4610_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___boxed(
    mut v_currentType_4617_: *mut LeanObject,
    mut v_value_4618_: *mut LeanObject,
    mut v_a_4619_: *mut LeanObject,
    mut v_a_4620_: *mut LeanObject,
    mut v_a_4621_: *mut LeanObject,
    mut v_a_4622_: *mut LeanObject,
    mut v_a_4623_: *mut LeanObject,
    mut v_a_4624_: *mut LeanObject,
    mut v_a_4625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4626_: *mut LeanObject = core::ptr::null_mut();
    v_res_4626_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_currentType_4617_, v_value_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
    lean_dec(v_a_4624_);
    lean_dec_ref(v_a_4623_);
    lean_dec(v_a_4622_);
    lean_dec_ref(v_a_4621_);
    lean_dec(v_a_4620_);
    lean_dec_ref(v_a_4619_);
    return v_res_4626_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(
    mut v_msg_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
    mut v___y_4633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4640_: u8 = 0;
    let mut v_toFunctor_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v___f_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4664_: u8 = 0;
    let mut v_toFunctor_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4671_: u8 = 0;
    let mut v___f_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_23546__overap_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4692_: u8 = 0;
    let mut v_unused_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4694_: u8 = 0;
    let mut v_unused_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut v_unused_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4700_: u8 = 0;
    let mut v_unused_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4635_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
                v___x_4636_ = l_StateRefT_x27_instMonad___redArg(v___x_4635_);
                v_toApplicative_4637_ = lean_ctor_get(v___x_4636_, 0);
                v_isSharedCheck_4700_ = (!lean_is_exclusive(v___x_4636_)) as u8;
                if v_isSharedCheck_4700_ == 0 {
                    v_unused_4701_ = lean_ctor_get(v___x_4636_, 1);
                    lean_dec(v_unused_4701_);
                    v___x_4639_ = v___x_4636_;
                    v_isShared_4640_ = v_isSharedCheck_4700_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4637_);
                    lean_dec(v___x_4636_);
                    v___x_4639_ = lean_box(0);
                    v_isShared_4640_ = v_isSharedCheck_4700_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4641_ = lean_ctor_get(v_toApplicative_4637_, 0);
                v_toSeq_4642_ = lean_ctor_get(v_toApplicative_4637_, 2);
                v_toSeqLeft_4643_ = lean_ctor_get(v_toApplicative_4637_, 3);
                v_toSeqRight_4644_ = lean_ctor_get(v_toApplicative_4637_, 4);
                v_isSharedCheck_4698_ = (!lean_is_exclusive(v_toApplicative_4637_)) as u8;
                if v_isSharedCheck_4698_ == 0 {
                    v_unused_4699_ = lean_ctor_get(v_toApplicative_4637_, 1);
                    lean_dec(v_unused_4699_);
                    v___x_4646_ = v_toApplicative_4637_;
                    v_isShared_4647_ = v_isSharedCheck_4698_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4644_);
                    lean_inc(v_toSeqLeft_4643_);
                    lean_inc(v_toSeq_4642_);
                    lean_inc(v_toFunctor_4641_);
                    lean_dec(v_toApplicative_4637_);
                    v___x_4646_ = lean_box(0);
                    v_isShared_4647_ = v_isSharedCheck_4698_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4648_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1;
                v___f_4649_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_4641_);
                v___f_4650_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4650_, 0, v_toFunctor_4641_);
                v___f_4651_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4651_, 0, v_toFunctor_4641_);
                v___x_4652_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4652_, 0, v___f_4650_);
                lean_ctor_set(v___x_4652_, 1, v___f_4651_);
                v___f_4653_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4653_, 0, v_toSeqRight_4644_);
                v___f_4654_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4654_, 0, v_toSeqLeft_4643_);
                v___f_4655_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4655_, 0, v_toSeq_4642_);
                if v_isShared_4647_ == 0 {
                    lean_ctor_set(v___x_4646_, 4, v___f_4653_);
                    lean_ctor_set(v___x_4646_, 3, v___f_4654_);
                    lean_ctor_set(v___x_4646_, 2, v___f_4655_);
                    lean_ctor_set(v___x_4646_, 1, v___f_4648_);
                    lean_ctor_set(v___x_4646_, 0, v___x_4652_);
                    v___x_4657_ = v___x_4646_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4652_);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 1, v___f_4648_);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 2, v___f_4655_);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 3, v___f_4654_);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 4, v___f_4653_);
                    v___x_4657_ = v_reuseFailAlloc_4697_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4640_ == 0 {
                    lean_ctor_set(v___x_4639_, 1, v___f_4649_);
                    lean_ctor_set(v___x_4639_, 0, v___x_4657_);
                    v___x_4659_ = v___x_4639_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4657_);
                    lean_ctor_set(v_reuseFailAlloc_4696_, 1, v___f_4649_);
                    v___x_4659_ = v_reuseFailAlloc_4696_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4660_ = l_StateRefT_x27_instMonad___redArg(v___x_4659_);
                v_toApplicative_4661_ = lean_ctor_get(v___x_4660_, 0);
                v_isSharedCheck_4694_ = (!lean_is_exclusive(v___x_4660_)) as u8;
                if v_isSharedCheck_4694_ == 0 {
                    v_unused_4695_ = lean_ctor_get(v___x_4660_, 1);
                    lean_dec(v_unused_4695_);
                    v___x_4663_ = v___x_4660_;
                    v_isShared_4664_ = v_isSharedCheck_4694_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4661_);
                    lean_dec(v___x_4660_);
                    v___x_4663_ = lean_box(0);
                    v_isShared_4664_ = v_isSharedCheck_4694_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4665_ = lean_ctor_get(v_toApplicative_4661_, 0);
                v_toSeq_4666_ = lean_ctor_get(v_toApplicative_4661_, 2);
                v_toSeqLeft_4667_ = lean_ctor_get(v_toApplicative_4661_, 3);
                v_toSeqRight_4668_ = lean_ctor_get(v_toApplicative_4661_, 4);
                v_isSharedCheck_4692_ = (!lean_is_exclusive(v_toApplicative_4661_)) as u8;
                if v_isSharedCheck_4692_ == 0 {
                    v_unused_4693_ = lean_ctor_get(v_toApplicative_4661_, 1);
                    lean_dec(v_unused_4693_);
                    v___x_4670_ = v_toApplicative_4661_;
                    v_isShared_4671_ = v_isSharedCheck_4692_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4668_);
                    lean_inc(v_toSeqLeft_4667_);
                    lean_inc(v_toSeq_4666_);
                    lean_inc(v_toFunctor_4665_);
                    lean_dec(v_toApplicative_4661_);
                    v___x_4670_ = lean_box(0);
                    v_isShared_4671_ = v_isSharedCheck_4692_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4672_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3;
                v___f_4673_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4;
                lean_inc_ref(v_toFunctor_4665_);
                v___f_4674_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4674_, 0, v_toFunctor_4665_);
                v___f_4675_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4675_, 0, v_toFunctor_4665_);
                v___x_4676_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4676_, 0, v___f_4674_);
                lean_ctor_set(v___x_4676_, 1, v___f_4675_);
                v___f_4677_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4677_, 0, v_toSeqRight_4668_);
                v___f_4678_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4678_, 0, v_toSeqLeft_4667_);
                v___f_4679_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4679_, 0, v_toSeq_4666_);
                if v_isShared_4671_ == 0 {
                    lean_ctor_set(v___x_4670_, 4, v___f_4677_);
                    lean_ctor_set(v___x_4670_, 3, v___f_4678_);
                    lean_ctor_set(v___x_4670_, 2, v___f_4679_);
                    lean_ctor_set(v___x_4670_, 1, v___f_4672_);
                    lean_ctor_set(v___x_4670_, 0, v___x_4676_);
                    v___x_4681_ = v___x_4670_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4676_);
                    lean_ctor_set(v_reuseFailAlloc_4691_, 1, v___f_4672_);
                    lean_ctor_set(v_reuseFailAlloc_4691_, 2, v___f_4679_);
                    lean_ctor_set(v_reuseFailAlloc_4691_, 3, v___f_4678_);
                    lean_ctor_set(v_reuseFailAlloc_4691_, 4, v___f_4677_);
                    v___x_4681_ = v_reuseFailAlloc_4691_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4664_ == 0 {
                    lean_ctor_set(v___x_4663_, 1, v___f_4673_);
                    lean_ctor_set(v___x_4663_, 0, v___x_4681_);
                    v___x_4683_ = v___x_4663_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4681_);
                    lean_ctor_set(v_reuseFailAlloc_4690_, 1, v___f_4673_);
                    v___x_4683_ = v_reuseFailAlloc_4690_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4684_ = l_StateRefT_x27_instMonad___redArg(v___x_4683_);
                v___x_4685_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
                v___x_4686_ = l_instInhabitedOfMonad___redArg(v___x_4684_, v___x_4685_);
                v___f_4687_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_4687_, 0, v___x_4686_);
                v___x_23546__overap_4688_ = lean_panic_fn_borrowed(v___f_4687_, v_msg_4627_);
                lean_dec_ref(v___f_4687_);
                lean_inc(v___y_4633_);
                lean_inc_ref(v___y_4632_);
                lean_inc(v___y_4631_);
                lean_inc_ref(v___y_4630_);
                lean_inc(v___y_4629_);
                lean_inc_ref(v___y_4628_);
                v___x_4689_ = lean_apply_7(
                    v___x_23546__overap_4688_,
                    v___y_4628_,
                    v___y_4629_,
                    v___y_4630_,
                    v___y_4631_,
                    v___y_4632_,
                    v___y_4633_,
                    lean_box(0),
                );
                return v___x_4689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0___boxed(
    mut v_msg_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
    mut v___y_4704_: *mut LeanObject,
    mut v___y_4705_: *mut LeanObject,
    mut v___y_4706_: *mut LeanObject,
    mut v___y_4707_: *mut LeanObject,
    mut v___y_4708_: *mut LeanObject,
    mut v___y_4709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4710_: *mut LeanObject = core::ptr::null_mut();
    v_res_4710_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v_msg_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
    lean_dec(v___y_4708_);
    lean_dec_ref(v___y_4707_);
    lean_dec(v___y_4706_);
    lean_dec_ref(v___y_4705_);
    lean_dec(v___y_4704_);
    lean_dec_ref(v___y_4703_);
    return v_res_4710_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(
    mut v_x_4711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    v___x_4712_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
    return v___x_4712_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed(
    mut v_x_4713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4714_: *mut LeanObject = core::ptr::null_mut();
    v_res_4714_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(v_x_4713_);
    lean_dec(v_x_4713_);
    return v_res_4714_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(
    mut v___x_4715_: u8,
    mut v_params_4716_: *mut LeanObject,
    mut v_i_4717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4720_: *mut LeanObject = core::ptr::null_mut();
    v___x_4718_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_4715_);
    v___x_4719_ = lean_array_get(v___x_4718_, v_params_4716_, v_i_4717_);
    lean_dec_ref(v___x_4718_);
    v_type_4720_ = lean_ctor_get(v___x_4719_, 2);
    lean_inc_ref(v_type_4720_);
    lean_dec(v___x_4719_);
    return v_type_4720_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed(
    mut v___x_4721_: *mut LeanObject,
    mut v_params_4722_: *mut LeanObject,
    mut v_i_4723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_24686__boxed_4724_: u8 = 0;
    let mut v_res_4725_: *mut LeanObject = core::ptr::null_mut();
    v___x_24686__boxed_4724_ = (lean_unbox(v___x_4721_) as u8);
    v_res_4725_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(v___x_24686__boxed_4724_, v_params_4722_, v_i_4723_);
    lean_dec(v_i_4723_);
    lean_dec_ref(v_params_4722_);
    return v_res_4725_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(
    mut v_fvarId_4726_: *mut LeanObject,
    mut v_code_4727_: *mut LeanObject,
    mut v_fvarId_4728_: *mut LeanObject,
    mut v___y_4729_: *mut LeanObject,
    mut v___y_4730_: *mut LeanObject,
    mut v___y_4731_: *mut LeanObject,
    mut v___y_4732_: *mut LeanObject,
    mut v___y_4733_: *mut LeanObject,
    mut v___y_4734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4736_: u8 = 0;
    v___x_4736_ = l_Lean_instBEqFVarId_beq(v_fvarId_4726_, v_fvarId_4728_);
    if v___x_4736_ == 0 {
        let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_code_4727_);
        v___x_4737_ = lean_alloc_ctor(5, 1, (0) as u32);
        lean_ctor_set(v___x_4737_, 0, v_fvarId_4728_);
        v___x_4738_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4738_, 0, v___x_4737_);
        return v___x_4738_;
    } else {
        let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fvarId_4728_);
        v___x_4739_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4739_, 0, v_code_4727_);
        return v___x_4739_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2___boxed(
    mut v_fvarId_4740_: *mut LeanObject,
    mut v_code_4741_: *mut LeanObject,
    mut v_fvarId_4742_: *mut LeanObject,
    mut v___y_4743_: *mut LeanObject,
    mut v___y_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
    mut v___y_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
    mut v___y_4749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4750_: *mut LeanObject = core::ptr::null_mut();
    v_res_4750_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_4740_, v_code_4741_, v_fvarId_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_);
    lean_dec(v___y_4748_);
    lean_dec_ref(v___y_4747_);
    lean_dec(v___y_4746_);
    lean_dec_ref(v___y_4745_);
    lean_dec(v___y_4744_);
    lean_dec_ref(v___y_4743_);
    lean_dec(v_fvarId_4740_);
    return v_res_4750_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(
    mut v_typeName_4751_: *mut LeanObject,
    mut v_a_4752_: *mut LeanObject,
    mut v_discr_4753_: *mut LeanObject,
    mut v_code_4754_: *mut LeanObject,
    mut v_alts_4755_: *mut LeanObject,
    mut v_resultType_4756_: *mut LeanObject,
    mut v_discr_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
    mut v___y_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
    mut v___y_4762_: *mut LeanObject,
    mut v___y_4763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currDeclResultType_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4771_: u8 = 0;
    let mut v___x_4772_: u8 = 0;
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: usize = 0;
    let mut v___x_4775_: usize = 0;
    let mut v___x_4776_: u8 = 0;
    let mut v___x_4777_: usize = 0;
    let mut v___x_4778_: usize = 0;
    let mut v___x_4779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currDeclResultType_4765_ = lean_ctor_get(v___y_4758_, 1);
                v___x_4774_ = lean_ptr_addr(v_alts_4755_);
                v___x_4775_ = lean_ptr_addr(v_a_4752_);
                v___x_4776_ = lean_usize_dec_eq(v___x_4774_, v___x_4775_);
                if v___x_4776_ == 0 {
                    v___y_4771_ = v___x_4776_;
                    state = 2;
                    continue;
                } else {
                    v___x_4777_ = lean_ptr_addr(v_resultType_4756_);
                    v___x_4778_ = lean_ptr_addr(v_currDeclResultType_4765_);
                    v___x_4779_ = lean_usize_dec_eq(v___x_4777_, v___x_4778_);
                    v___y_4771_ = v___x_4779_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_currDeclResultType_4765_);
                v___x_4767_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_4767_, 0, v_typeName_4751_);
                lean_ctor_set(v___x_4767_, 1, v_currDeclResultType_4765_);
                lean_ctor_set(v___x_4767_, 2, v_discr_4757_);
                lean_ctor_set(v___x_4767_, 3, v_a_4752_);
                v___x_4768_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_4768_, 0, v___x_4767_);
                v___x_4769_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4769_, 0, v___x_4768_);
                return v___x_4769_;
            }
            2 => {
                if v___y_4771_ == 0 {
                    lean_dec_ref(v_code_4754_);
                    state = 1;
                    continue;
                } else {
                    v___x_4772_ = l_Lean_instBEqFVarId_beq(v_discr_4753_, v_discr_4757_);
                    if v___x_4772_ == 0 {
                        lean_dec_ref(v_code_4754_);
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_discr_4757_);
                        lean_dec_ref(v_a_4752_);
                        lean_dec(v_typeName_4751_);
                        v___x_4773_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4773_, 0, v_code_4754_);
                        return v___x_4773_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1___boxed(
    mut v_typeName_4780_: *mut LeanObject,
    mut v_a_4781_: *mut LeanObject,
    mut v_discr_4782_: *mut LeanObject,
    mut v_code_4783_: *mut LeanObject,
    mut v_alts_4784_: *mut LeanObject,
    mut v_resultType_4785_: *mut LeanObject,
    mut v_discr_4786_: *mut LeanObject,
    mut v___y_4787_: *mut LeanObject,
    mut v___y_4788_: *mut LeanObject,
    mut v___y_4789_: *mut LeanObject,
    mut v___y_4790_: *mut LeanObject,
    mut v___y_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
    mut v___y_4793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4794_: *mut LeanObject = core::ptr::null_mut();
    v_res_4794_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_4780_, v_a_4781_, v_discr_4782_, v_code_4783_, v_alts_4784_, v_resultType_4785_, v_discr_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
    lean_dec(v___y_4792_);
    lean_dec_ref(v___y_4791_);
    lean_dec(v___y_4790_);
    lean_dec_ref(v___y_4789_);
    lean_dec(v___y_4788_);
    lean_dec_ref(v___y_4787_);
    lean_dec_ref(v_resultType_4785_);
    lean_dec_ref(v_alts_4784_);
    lean_dec(v_discr_4782_);
    return v_res_4794_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(
    mut v_alt_4795_: *mut LeanObject,
    mut v_f_4796_: *mut LeanObject,
    mut v___y_4797_: *mut LeanObject,
    mut v___y_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
    mut v___y_4801_: *mut LeanObject,
    mut v___y_4802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4810_: u8 = 0;
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_a_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4823_: u8 = 0;
    let mut v_code_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_alt_4795_) {
                0 => {
                    v_code_4824_ = lean_ctor_get(v_alt_4795_, 2);
                    lean_inc_ref(v_code_4824_);
                    v___y_4805_ = v_code_4824_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_4825_ = lean_ctor_get(v_alt_4795_, 1);
                    lean_inc_ref(v_code_4825_);
                    v___y_4805_ = v_code_4825_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_4826_ = lean_ctor_get(v_alt_4795_, 0);
                    lean_inc_ref(v_code_4826_);
                    v___y_4805_ = v_code_4826_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                lean_inc(v___y_4802_);
                lean_inc_ref(v___y_4801_);
                lean_inc(v___y_4800_);
                lean_inc_ref(v___y_4799_);
                lean_inc(v___y_4798_);
                lean_inc_ref(v___y_4797_);
                v___x_4806_ = lean_apply_8(
                    v_f_4796_,
                    v___y_4805_,
                    v___y_4797_,
                    v___y_4798_,
                    v___y_4799_,
                    v___y_4800_,
                    v___y_4801_,
                    v___y_4802_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4806_) == 0 {
                    v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
                    v_isSharedCheck_4815_ = (!lean_is_exclusive(v___x_4806_)) as u8;
                    if v_isSharedCheck_4815_ == 0 {
                        v___x_4809_ = v___x_4806_;
                        v_isShared_4810_ = v_isSharedCheck_4815_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4807_);
                        lean_dec(v___x_4806_);
                        v___x_4809_ = lean_box(0);
                        v_isShared_4810_ = v_isSharedCheck_4815_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_alt_4795_);
                    v_a_4816_ = lean_ctor_get(v___x_4806_, 0);
                    v_isSharedCheck_4823_ = (!lean_is_exclusive(v___x_4806_)) as u8;
                    if v_isSharedCheck_4823_ == 0 {
                        v___x_4818_ = v___x_4806_;
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4816_);
                        lean_dec(v___x_4806_);
                        v___x_4818_ = lean_box(0);
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4811_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_4795_, v_a_4807_);
                if v_isShared_4810_ == 0 {
                    lean_ctor_set(v___x_4809_, 0, v___x_4811_);
                    v___x_4813_ = v___x_4809_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4811_);
                    v___x_4813_ = v_reuseFailAlloc_4814_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4813_;
            }
            4 => {
                if v_isShared_4819_ == 0 {
                    v___x_4821_ = v___x_4818_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
                    v___x_4821_ = v_reuseFailAlloc_4822_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg___boxed(
    mut v_alt_4827_: *mut LeanObject,
    mut v_f_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
    mut v___y_4831_: *mut LeanObject,
    mut v___y_4832_: *mut LeanObject,
    mut v___y_4833_: *mut LeanObject,
    mut v___y_4834_: *mut LeanObject,
    mut v___y_4835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4836_: *mut LeanObject = core::ptr::null_mut();
    v_res_4836_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_4827_, v_f_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
    lean_dec(v___y_4834_);
    lean_dec_ref(v___y_4833_);
    lean_dec(v___y_4832_);
    lean_dec_ref(v___y_4831_);
    lean_dec(v___y_4830_);
    lean_dec_ref(v___y_4829_);
    return v_res_4836_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(
    mut v_fvarId_4837_: *mut LeanObject,
    mut v_i_4838_: *mut LeanObject,
    mut v_offset_4839_: *mut LeanObject,
    mut v_ty_4840_: *mut LeanObject,
    mut v_a_4841_: *mut LeanObject,
    mut v_y_4842_: *mut LeanObject,
    mut v_k_4843_: *mut LeanObject,
    mut v_code_4844_: *mut LeanObject,
    mut v_y_4845_: *mut LeanObject,
    mut v___y_4846_: *mut LeanObject,
    mut v___y_4847_: *mut LeanObject,
    mut v___y_4848_: *mut LeanObject,
    mut v___y_4849_: *mut LeanObject,
    mut v___y_4850_: *mut LeanObject,
    mut v___y_4851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4854_: u8 = 0;
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: u8 = 0;
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: usize = 0;
    let mut v___x_4861_: usize = 0;
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: usize = 0;
    let mut v___x_4866_: u8 = 0;
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: usize = 0;
    let mut v___x_4870_: usize = 0;
    let mut v___x_4871_: u8 = 0;
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: usize = 0;
    let mut v___x_4876_: u8 = 0;
    let mut v___x_4877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4875_ = lean_ptr_addr(v_fvarId_4837_);
                v___x_4876_ = lean_usize_dec_eq(v___x_4875_, v___x_4875_);
                if v___x_4876_ == 0 {
                    v___y_4854_ = v___x_4876_;
                    state = 1;
                    continue;
                } else {
                    v___x_4877_ = lean_nat_dec_eq(v_i_4838_, v_i_4838_);
                    v___y_4854_ = v___x_4877_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4854_ == 0 {
                    lean_dec_ref(v_code_4844_);
                    v___x_4855_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v___x_4855_, 0, v_fvarId_4837_);
                    lean_ctor_set(v___x_4855_, 1, v_i_4838_);
                    lean_ctor_set(v___x_4855_, 2, v_offset_4839_);
                    lean_ctor_set(v___x_4855_, 3, v_y_4845_);
                    lean_ctor_set(v___x_4855_, 4, v_ty_4840_);
                    lean_ctor_set(v___x_4855_, 5, v_a_4841_);
                    v___x_4856_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4856_, 0, v___x_4855_);
                    return v___x_4856_;
                } else {
                    v___x_4857_ = lean_nat_dec_eq(v_offset_4839_, v_offset_4839_);
                    if v___x_4857_ == 0 {
                        lean_dec_ref(v_code_4844_);
                        v___x_4858_ = lean_alloc_ctor(9, 6, (0) as u32);
                        lean_ctor_set(v___x_4858_, 0, v_fvarId_4837_);
                        lean_ctor_set(v___x_4858_, 1, v_i_4838_);
                        lean_ctor_set(v___x_4858_, 2, v_offset_4839_);
                        lean_ctor_set(v___x_4858_, 3, v_y_4845_);
                        lean_ctor_set(v___x_4858_, 4, v_ty_4840_);
                        lean_ctor_set(v___x_4858_, 5, v_a_4841_);
                        v___x_4859_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4859_, 0, v___x_4858_);
                        return v___x_4859_;
                    } else {
                        v___x_4860_ = lean_ptr_addr(v_y_4842_);
                        v___x_4861_ = lean_ptr_addr(v_y_4845_);
                        v___x_4862_ = lean_usize_dec_eq(v___x_4860_, v___x_4861_);
                        if v___x_4862_ == 0 {
                            lean_dec_ref(v_code_4844_);
                            v___x_4863_ = lean_alloc_ctor(9, 6, (0) as u32);
                            lean_ctor_set(v___x_4863_, 0, v_fvarId_4837_);
                            lean_ctor_set(v___x_4863_, 1, v_i_4838_);
                            lean_ctor_set(v___x_4863_, 2, v_offset_4839_);
                            lean_ctor_set(v___x_4863_, 3, v_y_4845_);
                            lean_ctor_set(v___x_4863_, 4, v_ty_4840_);
                            lean_ctor_set(v___x_4863_, 5, v_a_4841_);
                            v___x_4864_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4864_, 0, v___x_4863_);
                            return v___x_4864_;
                        } else {
                            v___x_4865_ = lean_ptr_addr(v_ty_4840_);
                            v___x_4866_ = lean_usize_dec_eq(v___x_4865_, v___x_4865_);
                            if v___x_4866_ == 0 {
                                lean_dec_ref(v_code_4844_);
                                v___x_4867_ = lean_alloc_ctor(9, 6, (0) as u32);
                                lean_ctor_set(v___x_4867_, 0, v_fvarId_4837_);
                                lean_ctor_set(v___x_4867_, 1, v_i_4838_);
                                lean_ctor_set(v___x_4867_, 2, v_offset_4839_);
                                lean_ctor_set(v___x_4867_, 3, v_y_4845_);
                                lean_ctor_set(v___x_4867_, 4, v_ty_4840_);
                                lean_ctor_set(v___x_4867_, 5, v_a_4841_);
                                v___x_4868_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4868_, 0, v___x_4867_);
                                return v___x_4868_;
                            } else {
                                v___x_4869_ = lean_ptr_addr(v_k_4843_);
                                v___x_4870_ = lean_ptr_addr(v_a_4841_);
                                v___x_4871_ = lean_usize_dec_eq(v___x_4869_, v___x_4870_);
                                if v___x_4871_ == 0 {
                                    lean_dec_ref(v_code_4844_);
                                    v___x_4872_ = lean_alloc_ctor(9, 6, (0) as u32);
                                    lean_ctor_set(v___x_4872_, 0, v_fvarId_4837_);
                                    lean_ctor_set(v___x_4872_, 1, v_i_4838_);
                                    lean_ctor_set(v___x_4872_, 2, v_offset_4839_);
                                    lean_ctor_set(v___x_4872_, 3, v_y_4845_);
                                    lean_ctor_set(v___x_4872_, 4, v_ty_4840_);
                                    lean_ctor_set(v___x_4872_, 5, v_a_4841_);
                                    v___x_4873_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_4873_, 0, v___x_4872_);
                                    return v___x_4873_;
                                } else {
                                    lean_dec(v_y_4845_);
                                    lean_dec_ref(v_a_4841_);
                                    lean_dec_ref(v_ty_4840_);
                                    lean_dec(v_offset_4839_);
                                    lean_dec(v_i_4838_);
                                    lean_dec(v_fvarId_4837_);
                                    v___x_4874_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_4874_, 0, v_code_4844_);
                                    return v___x_4874_;
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4___boxed(
    mut v_fvarId_4878_: *mut LeanObject,
    mut v_i_4879_: *mut LeanObject,
    mut v_offset_4880_: *mut LeanObject,
    mut v_ty_4881_: *mut LeanObject,
    mut v_a_4882_: *mut LeanObject,
    mut v_y_4883_: *mut LeanObject,
    mut v_k_4884_: *mut LeanObject,
    mut v_code_4885_: *mut LeanObject,
    mut v_y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
    mut v___y_4891_: *mut LeanObject,
    mut v___y_4892_: *mut LeanObject,
    mut v___y_4893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4894_: *mut LeanObject = core::ptr::null_mut();
    v_res_4894_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_4878_, v_i_4879_, v_offset_4880_, v_ty_4881_, v_a_4882_, v_y_4883_, v_k_4884_, v_code_4885_, v_y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
    lean_dec(v___y_4892_);
    lean_dec_ref(v___y_4891_);
    lean_dec(v___y_4890_);
    lean_dec_ref(v___y_4889_);
    lean_dec(v___y_4888_);
    lean_dec_ref(v___y_4887_);
    lean_dec_ref(v_k_4884_);
    lean_dec(v_y_4883_);
    return v_res_4894_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(
    mut v_fvarId_4895_: *mut LeanObject,
    mut v_i_4896_: *mut LeanObject,
    mut v_a_4897_: *mut LeanObject,
    mut v_y_4898_: *mut LeanObject,
    mut v_k_4899_: *mut LeanObject,
    mut v_code_4900_: *mut LeanObject,
    mut v_y_4901_: *mut LeanObject,
    mut v___y_4902_: *mut LeanObject,
    mut v___y_4903_: *mut LeanObject,
    mut v___y_4904_: *mut LeanObject,
    mut v___y_4905_: *mut LeanObject,
    mut v___y_4906_: *mut LeanObject,
    mut v___y_4907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4910_: u8 = 0;
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: usize = 0;
    let mut v___x_4914_: usize = 0;
    let mut v___x_4915_: u8 = 0;
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: usize = 0;
    let mut v___x_4919_: usize = 0;
    let mut v___x_4920_: u8 = 0;
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: usize = 0;
    let mut v___x_4925_: u8 = 0;
    let mut v___x_4926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4924_ = lean_ptr_addr(v_fvarId_4895_);
                v___x_4925_ = lean_usize_dec_eq(v___x_4924_, v___x_4924_);
                if v___x_4925_ == 0 {
                    v___y_4910_ = v___x_4925_;
                    state = 1;
                    continue;
                } else {
                    v___x_4926_ = lean_nat_dec_eq(v_i_4896_, v_i_4896_);
                    v___y_4910_ = v___x_4926_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4910_ == 0 {
                    lean_dec_ref(v_code_4900_);
                    v___x_4911_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v___x_4911_, 0, v_fvarId_4895_);
                    lean_ctor_set(v___x_4911_, 1, v_i_4896_);
                    lean_ctor_set(v___x_4911_, 2, v_y_4901_);
                    lean_ctor_set(v___x_4911_, 3, v_a_4897_);
                    v___x_4912_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4912_, 0, v___x_4911_);
                    return v___x_4912_;
                } else {
                    v___x_4913_ = lean_ptr_addr(v_y_4898_);
                    v___x_4914_ = lean_ptr_addr(v_y_4901_);
                    v___x_4915_ = lean_usize_dec_eq(v___x_4913_, v___x_4914_);
                    if v___x_4915_ == 0 {
                        lean_dec_ref(v_code_4900_);
                        v___x_4916_ = lean_alloc_ctor(8, 4, (0) as u32);
                        lean_ctor_set(v___x_4916_, 0, v_fvarId_4895_);
                        lean_ctor_set(v___x_4916_, 1, v_i_4896_);
                        lean_ctor_set(v___x_4916_, 2, v_y_4901_);
                        lean_ctor_set(v___x_4916_, 3, v_a_4897_);
                        v___x_4917_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4917_, 0, v___x_4916_);
                        return v___x_4917_;
                    } else {
                        v___x_4918_ = lean_ptr_addr(v_k_4899_);
                        v___x_4919_ = lean_ptr_addr(v_a_4897_);
                        v___x_4920_ = lean_usize_dec_eq(v___x_4918_, v___x_4919_);
                        if v___x_4920_ == 0 {
                            lean_dec_ref(v_code_4900_);
                            v___x_4921_ = lean_alloc_ctor(8, 4, (0) as u32);
                            lean_ctor_set(v___x_4921_, 0, v_fvarId_4895_);
                            lean_ctor_set(v___x_4921_, 1, v_i_4896_);
                            lean_ctor_set(v___x_4921_, 2, v_y_4901_);
                            lean_ctor_set(v___x_4921_, 3, v_a_4897_);
                            v___x_4922_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4922_, 0, v___x_4921_);
                            return v___x_4922_;
                        } else {
                            lean_dec(v_y_4901_);
                            lean_dec_ref(v_a_4897_);
                            lean_dec(v_i_4896_);
                            lean_dec(v_fvarId_4895_);
                            v___x_4923_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4923_, 0, v_code_4900_);
                            return v___x_4923_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3___boxed(
    mut v_fvarId_4927_: *mut LeanObject,
    mut v_i_4928_: *mut LeanObject,
    mut v_a_4929_: *mut LeanObject,
    mut v_y_4930_: *mut LeanObject,
    mut v_k_4931_: *mut LeanObject,
    mut v_code_4932_: *mut LeanObject,
    mut v_y_4933_: *mut LeanObject,
    mut v___y_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
    mut v___y_4936_: *mut LeanObject,
    mut v___y_4937_: *mut LeanObject,
    mut v___y_4938_: *mut LeanObject,
    mut v___y_4939_: *mut LeanObject,
    mut v___y_4940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4941_: *mut LeanObject = core::ptr::null_mut();
    v_res_4941_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_4927_, v_i_4928_, v_a_4929_, v_y_4930_, v_k_4931_, v_code_4932_, v_y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_);
    lean_dec(v___y_4939_);
    lean_dec_ref(v___y_4938_);
    lean_dec(v___y_4937_);
    lean_dec_ref(v___y_4936_);
    lean_dec(v___y_4935_);
    lean_dec_ref(v___y_4934_);
    lean_dec_ref(v_k_4931_);
    lean_dec(v_y_4930_);
    return v_res_4941_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(
    mut v___x_4942_: u8,
    mut v_params_4943_: *mut LeanObject,
    mut v_i_4944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4947_: *mut LeanObject = core::ptr::null_mut();
    v___x_4945_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_4942_);
    v___x_4946_ = lean_array_get(v___x_4945_, v_params_4943_, v_i_4944_);
    lean_dec_ref(v___x_4945_);
    v_type_4947_ = lean_ctor_get(v___x_4946_, 2);
    lean_inc_ref(v_type_4947_);
    lean_dec(v___x_4946_);
    return v_type_4947_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed(
    mut v___x_4948_: *mut LeanObject,
    mut v_params_4949_: *mut LeanObject,
    mut v_i_4950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_25023__boxed_4951_: u8 = 0;
    let mut v_res_4952_: *mut LeanObject = core::ptr::null_mut();
    v___x_25023__boxed_4951_ = (lean_unbox(v___x_4948_) as u8);
    v_res_4952_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(v___x_25023__boxed_4951_, v_params_4949_, v_i_4950_);
    lean_dec(v_i_4950_);
    lean_dec_ref(v_params_4949_);
    return v_res_4952_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1()
-> *mut LeanObject {
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    v___x_4954_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2;
    v___x_4955_ = lean_unsigned_to_nat(44);
    v___x_4956_ = lean_unsigned_to_nat(353);
    v___x_4957_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0;
    v___x_4958_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0;
    v___x_4959_ = l_mkPanicMessageWithDecl(
        v___x_4958_,
        v___x_4957_,
        v___x_4956_,
        v___x_4955_,
        v___x_4954_,
    );
    return v___x_4959_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3()
-> *mut LeanObject {
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    v___x_4961_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2;
    v___x_4962_ = lean_unsigned_to_nat(45);
    v___x_4963_ = lean_unsigned_to_nat(336);
    v___x_4964_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0;
    v___x_4965_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0;
    v___x_4966_ = l_mkPanicMessageWithDecl(
        v___x_4965_,
        v___x_4964_,
        v___x_4963_,
        v___x_4962_,
        v___x_4961_,
    );
    return v___x_4966_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4()
-> *mut LeanObject {
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    v___x_4967_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2;
    v___x_4968_ = lean_unsigned_to_nat(45);
    v___x_4969_ = lean_unsigned_to_nat(341);
    v___x_4970_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0;
    v___x_4971_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0;
    v___x_4972_ = l_mkPanicMessageWithDecl(
        v___x_4971_,
        v___x_4970_,
        v___x_4969_,
        v___x_4968_,
        v___x_4967_,
    );
    return v___x_4972_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(
    mut v_code_4973_: *mut LeanObject,
    mut v_decl_4974_: *mut LeanObject,
    mut v_k_4975_: *mut LeanObject,
    mut v_a_4976_: *mut LeanObject,
    mut v_a_4977_: *mut LeanObject,
    mut v_a_4978_: *mut LeanObject,
    mut v_a_4979_: *mut LeanObject,
    mut v_a_4980_: *mut LeanObject,
    mut v_a_4981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v___x_4999_: u8 = 0;
    let mut v___y_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5016_: u8 = 0;
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5021_: u8 = 0;
    let mut v___y_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5025_: u8 = 0;
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5030_: u8 = 0;
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5034_: u8 = 0;
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5044_: u8 = 0;
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: usize = 0;
    let mut v___x_5060_: usize = 0;
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: usize = 0;
    let mut v___x_5063_: usize = 0;
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5067_: u8 = 0;
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5073_: u8 = 0;
    let mut v_unused_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5078_: u8 = 0;
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5082_: u8 = 0;
    let mut v_args_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5096_: u8 = 0;
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5101_: u8 = 0;
    let mut v_a_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5105_: u8 = 0;
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5109_: u8 = 0;
    let mut v_a_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5113_: u8 = 0;
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5117_: u8 = 0;
    let mut v_i_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5122_: u8 = 0;
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: usize = 0;
    let mut v___x_5133_: usize = 0;
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: usize = 0;
    let mut v___x_5136_: usize = 0;
    let mut v___x_5137_: u8 = 0;
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5143_: u8 = 0;
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5147_: u8 = 0;
    let mut v_a_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5151_: u8 = 0;
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5155_: u8 = 0;
    let mut v_cidx_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: usize = 0;
    let mut v___x_5164_: usize = 0;
    let mut v___x_5165_: u8 = 0;
    let mut v___x_5166_: usize = 0;
    let mut v___x_5167_: usize = 0;
    let mut v___x_5168_: u8 = 0;
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5171_: u8 = 0;
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5177_: u8 = 0;
    let mut v_unused_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5182_: u8 = 0;
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut v___x_5187_: u8 = 0;
    let mut v___x_5188_: u8 = 0;
    let mut v_fn_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5209_: u8 = 0;
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut v_a_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5218_: u8 = 0;
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5222_: u8 = 0;
    let mut v_a_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5226_: u8 = 0;
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5230_: u8 = 0;
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5236_: u8 = 0;
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5240_: u8 = 0;
    let mut v_fn_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: usize = 0;
    let mut v___x_5261_: usize = 0;
    let mut v___x_5262_: u8 = 0;
    let mut v___x_5263_: usize = 0;
    let mut v___x_5264_: usize = 0;
    let mut v___x_5265_: u8 = 0;
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5271_: u8 = 0;
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut v_a_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v___x_5284_: u8 = 0;
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5293_: u8 = 0;
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5299_: u8 = 0;
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5303_: u8 = 0;
    let mut v_args_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5318_: u8 = 0;
    let mut v___y_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5326_: u8 = 0;
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: usize = 0;
    let mut v___x_5333_: usize = 0;
    let mut v___x_5334_: u8 = 0;
    let mut v___x_5335_: usize = 0;
    let mut v___x_5336_: usize = 0;
    let mut v___x_5337_: u8 = 0;
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5340_: u8 = 0;
    let mut v_a_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5344_: u8 = 0;
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5348_: u8 = 0;
    let mut v_isSharedCheck_5349_: u8 = 0;
    let mut v_a_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5353_: u8 = 0;
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5357_: u8 = 0;
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___y_5366_: u8 = 0;
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: usize = 0;
    let mut v___x_5377_: usize = 0;
    let mut v___x_5378_: u8 = 0;
    let mut v___x_5379_: usize = 0;
    let mut v___x_5380_: usize = 0;
    let mut v___x_5381_: u8 = 0;
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5385_: u8 = 0;
    let mut v_a_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5389_: u8 = 0;
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut v_isSharedCheck_5394_: u8 = 0;
    let mut v_isSharedCheck_5395_: u8 = 0;
    let mut v_a_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5399_: u8 = 0;
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5403_: u8 = 0;
    let mut v_isSharedCheck_5404_: u8 = 0;
    let mut v_a_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5408_: u8 = 0;
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_4992_ = lean_ctor_get(v_decl_4974_, 2);
                v_value_4993_ = lean_ctor_get(v_decl_4974_, 3);
                lean_inc_n(v_value_4993_, 2);
                lean_inc_ref(v_type_4992_);
                v___x_4994_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_type_4992_, v_value_4993_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                if lean_obj_tag(v___x_4994_) == 0 {
                    v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
                    v_isSharedCheck_5404_ = (!lean_is_exclusive(v___x_4994_)) as u8;
                    if v_isSharedCheck_5404_ == 0 {
                        v___x_4997_ = v___x_4994_;
                        v_isShared_4998_ = v_isSharedCheck_5404_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4995_);
                        lean_dec(v___x_4994_);
                        v___x_4997_ = lean_box(0);
                        v_isShared_4998_ = v_isSharedCheck_5404_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_4993_);
                    lean_dec_ref(v_k_4975_);
                    lean_dec_ref(v_decl_4974_);
                    lean_dec_ref(v_code_4973_);
                    v_a_5405_ = lean_ctor_get(v___x_4994_, 0);
                    v_isSharedCheck_5412_ = (!lean_is_exclusive(v___x_4994_)) as u8;
                    if v_isSharedCheck_5412_ == 0 {
                        v___x_5407_ = v___x_4994_;
                        v_isShared_5408_ = v_isSharedCheck_5412_;
                        state = 71;
                        continue;
                    } else {
                        lean_inc(v_a_5405_);
                        lean_dec(v___x_4994_);
                        v___x_5407_ = lean_box(0);
                        v_isShared_5408_ = v_isSharedCheck_5412_;
                        state = 71;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4990_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
                v___x_4991_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_4990_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
                return v___x_4991_;
            }
            2 => {
                v___x_4999_ = 1;
                lean_inc(v_a_4995_);
                v___x_5012_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_4999_, v_decl_4974_, v_a_4995_, v_value_4993_, v_a_4979_);
                if lean_obj_tag(v___x_5012_) == 0 {
                    v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
                    v_isSharedCheck_5395_ = (!lean_is_exclusive(v___x_5012_)) as u8;
                    if v_isSharedCheck_5395_ == 0 {
                        v___x_5015_ = v___x_5012_;
                        v_isShared_5016_ = v_isSharedCheck_5395_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5013_);
                        lean_dec(v___x_5012_);
                        v___x_5015_ = lean_box(0);
                        v_isShared_5016_ = v_isSharedCheck_5395_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4997_);
                    lean_dec(v_a_4995_);
                    lean_dec_ref(v_k_4975_);
                    lean_dec_ref(v_code_4973_);
                    v_a_5396_ = lean_ctor_get(v___x_5012_, 0);
                    v_isSharedCheck_5403_ = (!lean_is_exclusive(v___x_5012_)) as u8;
                    if v_isSharedCheck_5403_ == 0 {
                        v___x_5398_ = v___x_5012_;
                        v_isShared_5399_ = v_isSharedCheck_5403_;
                        state = 69;
                        continue;
                    } else {
                        lean_inc(v_a_5396_);
                        lean_dec(v___x_5012_);
                        v___x_5398_ = lean_box(0);
                        v_isShared_5399_ = v_isSharedCheck_5403_;
                        state = 69;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5003_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4999_, v___y_5001_, v___y_5002_);
                lean_dec_ref(v___y_5001_);
                if v_isShared_4998_ == 0 {
                    lean_ctor_set(v___x_4997_, 0, v___x_5003_);
                    v___x_5005_ = v___x_4997_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_5003_);
                    v___x_5005_ = v_reuseFailAlloc_5006_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5005_;
            }
            5 => {
                v___x_5010_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4999_, v___y_5008_, v___y_5009_);
                lean_dec_ref(v___y_5008_);
                v___x_5011_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5011_, 0, v___x_5010_);
                return v___x_5011_;
            }
            6 => {
                v___x_5017_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                if lean_obj_tag(v___x_5017_) == 0 {
                    v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
                    v_isSharedCheck_5394_ = (!lean_is_exclusive(v___x_5017_)) as u8;
                    if v_isSharedCheck_5394_ == 0 {
                        v___x_5020_ = v___x_5017_;
                        v_isShared_5021_ = v_isSharedCheck_5394_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5018_);
                        lean_dec(v___x_5017_);
                        v___x_5020_ = lean_box(0);
                        v_isShared_5021_ = v_isSharedCheck_5394_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5015_);
                    lean_dec(v_a_5013_);
                    lean_del_object(v___x_4997_);
                    lean_dec(v_a_4995_);
                    lean_dec_ref(v_code_4973_);
                    return v___x_5017_;
                }
            }
            7 => {
                v_value_5052_ = lean_ctor_get(v_a_5013_, 3);
                match lean_obj_tag(v_value_5052_) {
                    4 => {
                        lean_del_object(v___x_5020_);
                        lean_del_object(v___x_5015_);
                        lean_del_object(v___x_4997_);
                        lean_dec(v_a_4995_);
                        v_args_5083_ = lean_ctor_get(v_value_5052_, 1);
                        v___f_5084_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2;
                        v___x_5085_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_5083_, v___f_5084_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                        if lean_obj_tag(v___x_5085_) == 0 {
                            v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
                            lean_inc(v_a_5086_);
                            lean_dec_ref_known(v___x_5085_, 1);
                            v_fst_5087_ = lean_ctor_get(v_a_5086_, 0);
                            lean_inc(v_fst_5087_);
                            v_snd_5088_ = lean_ctor_get(v_a_5086_, 1);
                            lean_inc(v_snd_5088_);
                            lean_dec(v_a_5086_);
                            lean_inc_ref(v_value_5052_);
                            v___x_5089_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_4999_, v_value_5052_, v_fst_5087_);
                            v___x_5090_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                                v___x_4999_,
                                v_a_5013_,
                                v___x_5089_,
                                v_a_4979_,
                            );
                            if lean_obj_tag(v___x_5090_) == 0 {
                                v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
                                lean_inc(v_a_5091_);
                                lean_dec_ref_known(v___x_5090_, 1);
                                v___x_5092_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_4973_, v_a_5091_, v_a_5018_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                                if lean_obj_tag(v___x_5092_) == 0 {
                                    v_a_5093_ = lean_ctor_get(v___x_5092_, 0);
                                    v_isSharedCheck_5101_ = (!lean_is_exclusive(v___x_5092_)) as u8;
                                    if v_isSharedCheck_5101_ == 0 {
                                        v___x_5095_ = v___x_5092_;
                                        v_isShared_5096_ = v_isSharedCheck_5101_;
                                        state = 21;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5093_);
                                        lean_dec(v___x_5092_);
                                        v___x_5095_ = lean_box(0);
                                        v_isShared_5096_ = v_isSharedCheck_5101_;
                                        state = 21;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_snd_5088_);
                                    return v___x_5092_;
                                }
                            } else {
                                lean_dec(v_snd_5088_);
                                lean_dec(v_a_5018_);
                                lean_dec_ref(v_code_4973_);
                                v_a_5102_ = lean_ctor_get(v___x_5090_, 0);
                                v_isSharedCheck_5109_ = (!lean_is_exclusive(v___x_5090_)) as u8;
                                if v_isSharedCheck_5109_ == 0 {
                                    v___x_5104_ = v___x_5090_;
                                    v_isShared_5105_ = v_isSharedCheck_5109_;
                                    state = 23;
                                    continue;
                                } else {
                                    lean_inc(v_a_5102_);
                                    lean_dec(v___x_5090_);
                                    v___x_5104_ = lean_box(0);
                                    v_isShared_5105_ = v_isSharedCheck_5109_;
                                    state = 23;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5018_);
                            lean_dec(v_a_5013_);
                            lean_dec_ref(v_code_4973_);
                            v_a_5110_ = lean_ctor_get(v___x_5085_, 0);
                            v_isSharedCheck_5117_ = (!lean_is_exclusive(v___x_5085_)) as u8;
                            if v_isSharedCheck_5117_ == 0 {
                                v___x_5112_ = v___x_5085_;
                                v_isShared_5113_ = v_isSharedCheck_5117_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_5110_);
                                lean_dec(v___x_5085_);
                                v___x_5112_ = lean_box(0);
                                v_isShared_5113_ = v_isSharedCheck_5117_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                    5 => {
                        lean_del_object(v___x_5015_);
                        v_i_5118_ = lean_ctor_get(v_value_5052_, 0);
                        v_args_5119_ = lean_ctor_get(v_value_5052_, 1);
                        v___f_5120_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2;
                        v___x_5187_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_i_5118_);
                        if v___x_5187_ == 0 {
                            v___y_5122_ = v___x_5187_;
                            state = 27;
                            continue;
                        } else {
                            v___x_5188_ =
                                l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_4995_);
                            v___y_5122_ = v___x_5188_;
                            state = 27;
                            continue;
                        }
                    }
                    6 => {
                        lean_inc_ref(v_value_5052_);
                        lean_del_object(v___x_5020_);
                        lean_del_object(v___x_4997_);
                        v___y_5054_ = v_a_4979_;
                        state = 16;
                        continue;
                    }
                    7 => {
                        lean_inc_ref(v_value_5052_);
                        lean_del_object(v___x_5020_);
                        lean_del_object(v___x_4997_);
                        v___y_5054_ = v_a_4979_;
                        state = 16;
                        continue;
                    }
                    9 => {
                        lean_del_object(v___x_5020_);
                        lean_del_object(v___x_5015_);
                        lean_del_object(v___x_4997_);
                        lean_dec(v_a_4995_);
                        v_fn_5189_ = lean_ctor_get(v_value_5052_, 0);
                        v_args_5190_ = lean_ctor_get(v_value_5052_, 1);
                        lean_inc(v_fn_5189_);
                        v___x_5191_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(
                            v_fn_5189_, v_a_4981_,
                        );
                        if lean_obj_tag(v___x_5191_) == 0 {
                            v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
                            lean_inc(v_a_5192_);
                            lean_dec_ref_known(v___x_5191_, 1);
                            if lean_obj_tag(v_a_5192_) == 1 {
                                v_val_5193_ = lean_ctor_get(v_a_5192_, 0);
                                lean_inc(v_val_5193_);
                                lean_dec_ref_known(v_a_5192_, 1);
                                v_type_5194_ = lean_ctor_get(v_val_5193_, 2);
                                lean_inc_ref(v_type_5194_);
                                v_params_5195_ = lean_ctor_get(v_val_5193_, 3);
                                lean_inc_ref(v_params_5195_);
                                lean_dec(v_val_5193_);
                                v___x_5196_ = lean_box((v___x_4999_) as usize);
                                v___f_5197_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
                                lean_closure_set(v___f_5197_, 0, v___x_5196_);
                                lean_closure_set(v___f_5197_, 1, v_params_5195_);
                                v___x_5198_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_5190_, v___f_5197_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                                if lean_obj_tag(v___x_5198_) == 0 {
                                    v_a_5199_ = lean_ctor_get(v___x_5198_, 0);
                                    lean_inc(v_a_5199_);
                                    lean_dec_ref_known(v___x_5198_, 1);
                                    v_fst_5200_ = lean_ctor_get(v_a_5199_, 0);
                                    lean_inc(v_fst_5200_);
                                    v_snd_5201_ = lean_ctor_get(v_a_5199_, 1);
                                    lean_inc(v_snd_5201_);
                                    lean_dec(v_a_5199_);
                                    lean_inc_ref(v_value_5052_);
                                    v___x_5202_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_4999_, v_value_5052_, v_fst_5200_);
                                    v___x_5203_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                                        v___x_4999_,
                                        v_a_5013_,
                                        v___x_5202_,
                                        v_a_4979_,
                                    );
                                    if lean_obj_tag(v___x_5203_) == 0 {
                                        v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
                                        lean_inc(v_a_5204_);
                                        lean_dec_ref_known(v___x_5203_, 1);
                                        v___x_5205_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_4973_, v_a_5204_, v_type_5194_, v_a_5018_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                                        lean_dec_ref(v_type_5194_);
                                        if lean_obj_tag(v___x_5205_) == 0 {
                                            v_a_5206_ = lean_ctor_get(v___x_5205_, 0);
                                            v_isSharedCheck_5214_ =
                                                (!lean_is_exclusive(v___x_5205_)) as u8;
                                            if v_isSharedCheck_5214_ == 0 {
                                                v___x_5208_ = v___x_5205_;
                                                v_isShared_5209_ = v_isSharedCheck_5214_;
                                                state = 36;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5206_);
                                                lean_dec(v___x_5205_);
                                                v___x_5208_ = lean_box(0);
                                                v_isShared_5209_ = v_isSharedCheck_5214_;
                                                state = 36;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_snd_5201_);
                                            return v___x_5205_;
                                        }
                                    } else {
                                        lean_dec(v_snd_5201_);
                                        lean_dec_ref(v_type_5194_);
                                        lean_dec(v_a_5018_);
                                        lean_dec_ref(v_code_4973_);
                                        v_a_5215_ = lean_ctor_get(v___x_5203_, 0);
                                        v_isSharedCheck_5222_ =
                                            (!lean_is_exclusive(v___x_5203_)) as u8;
                                        if v_isSharedCheck_5222_ == 0 {
                                            v___x_5217_ = v___x_5203_;
                                            v_isShared_5218_ = v_isSharedCheck_5222_;
                                            state = 38;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5215_);
                                            lean_dec(v___x_5203_);
                                            v___x_5217_ = lean_box(0);
                                            v_isShared_5218_ = v_isSharedCheck_5222_;
                                            state = 38;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_type_5194_);
                                    lean_dec(v_a_5018_);
                                    lean_dec(v_a_5013_);
                                    lean_dec_ref(v_code_4973_);
                                    v_a_5223_ = lean_ctor_get(v___x_5198_, 0);
                                    v_isSharedCheck_5230_ = (!lean_is_exclusive(v___x_5198_)) as u8;
                                    if v_isSharedCheck_5230_ == 0 {
                                        v___x_5225_ = v___x_5198_;
                                        v_isShared_5226_ = v_isSharedCheck_5230_;
                                        state = 40;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5223_);
                                        lean_dec(v___x_5198_);
                                        v___x_5225_ = lean_box(0);
                                        v_isShared_5226_ = v_isSharedCheck_5230_;
                                        state = 40;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5192_);
                                lean_dec(v_a_5018_);
                                lean_dec(v_a_5013_);
                                lean_dec_ref(v_code_4973_);
                                v___x_5231_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3);
                                v___x_5232_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_5231_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                                return v___x_5232_;
                            }
                        } else {
                            lean_dec(v_a_5018_);
                            lean_dec(v_a_5013_);
                            lean_dec_ref(v_code_4973_);
                            v_a_5233_ = lean_ctor_get(v___x_5191_, 0);
                            v_isSharedCheck_5240_ = (!lean_is_exclusive(v___x_5191_)) as u8;
                            if v_isSharedCheck_5240_ == 0 {
                                v___x_5235_ = v___x_5191_;
                                v_isShared_5236_ = v_isSharedCheck_5240_;
                                state = 42;
                                continue;
                            } else {
                                lean_inc(v_a_5233_);
                                lean_dec(v___x_5191_);
                                v___x_5235_ = lean_box(0);
                                v_isShared_5236_ = v_isSharedCheck_5240_;
                                state = 42;
                                continue;
                            }
                        }
                    }
                    10 => {
                        lean_del_object(v___x_5020_);
                        lean_del_object(v___x_5015_);
                        lean_del_object(v___x_4997_);
                        lean_dec(v_a_4995_);
                        v_fn_5241_ = lean_ctor_get(v_value_5052_, 0);
                        v_args_5242_ = lean_ctor_get(v_value_5052_, 1);
                        lean_inc(v_fn_5241_);
                        v___x_5243_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(
                            v_fn_5241_, v_a_4981_,
                        );
                        if lean_obj_tag(v___x_5243_) == 0 {
                            v_a_5244_ = lean_ctor_get(v___x_5243_, 0);
                            lean_inc(v_a_5244_);
                            lean_dec_ref_known(v___x_5243_, 1);
                            if lean_obj_tag(v_a_5244_) == 1 {
                                v_val_5245_ = lean_ctor_get(v_a_5244_, 0);
                                lean_inc(v_val_5245_);
                                lean_dec_ref_known(v_a_5244_, 1);
                                v___x_5246_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_val_5245_, v_a_4981_);
                                if lean_obj_tag(v___x_5246_) == 0 {
                                    v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
                                    lean_inc(v_a_5247_);
                                    lean_dec_ref_known(v___x_5246_, 1);
                                    v___f_5248_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2;
                                    v___x_5284_ = (lean_unbox(v_a_5247_) as u8);
                                    lean_dec(v_a_5247_);
                                    if v___x_5284_ == 0 {
                                        lean_inc(v_fn_5241_);
                                        v___y_5250_ = v_fn_5241_;
                                        state = 44;
                                        continue;
                                    } else {
                                        lean_inc(v_fn_5241_);
                                        v___x_5285_ = l_Lean_Compiler_LCNF_mkBoxedName(v_fn_5241_);
                                        v___y_5250_ = v___x_5285_;
                                        state = 44;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_5018_);
                                    lean_dec(v_a_5013_);
                                    lean_dec_ref(v_code_4973_);
                                    v_a_5286_ = lean_ctor_get(v___x_5246_, 0);
                                    v_isSharedCheck_5293_ = (!lean_is_exclusive(v___x_5246_)) as u8;
                                    if v_isSharedCheck_5293_ == 0 {
                                        v___x_5288_ = v___x_5246_;
                                        v_isShared_5289_ = v_isSharedCheck_5293_;
                                        state = 49;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5286_);
                                        lean_dec(v___x_5246_);
                                        v___x_5288_ = lean_box(0);
                                        v_isShared_5289_ = v_isSharedCheck_5293_;
                                        state = 49;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5244_);
                                lean_dec(v_a_5018_);
                                lean_dec(v_a_5013_);
                                lean_dec_ref(v_code_4973_);
                                v___x_5294_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
                                v___x_5295_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_5294_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                                return v___x_5295_;
                            }
                        } else {
                            lean_dec(v_a_5018_);
                            lean_dec(v_a_5013_);
                            lean_dec_ref(v_code_4973_);
                            v_a_5296_ = lean_ctor_get(v___x_5243_, 0);
                            v_isSharedCheck_5303_ = (!lean_is_exclusive(v___x_5243_)) as u8;
                            if v_isSharedCheck_5303_ == 0 {
                                v___x_5298_ = v___x_5243_;
                                v_isShared_5299_ = v_isSharedCheck_5303_;
                                state = 51;
                                continue;
                            } else {
                                lean_inc(v_a_5296_);
                                lean_dec(v___x_5243_);
                                v___x_5298_ = lean_box(0);
                                v_isShared_5299_ = v_isSharedCheck_5303_;
                                state = 51;
                                continue;
                            }
                        }
                    }
                    11 => {
                        lean_inc_ref(v_value_5052_);
                        lean_del_object(v___x_5020_);
                        lean_del_object(v___x_4997_);
                        v___y_5054_ = v_a_4979_;
                        state = 16;
                        continue;
                    }
                    12 => {
                        lean_del_object(v___x_5020_);
                        lean_del_object(v___x_5015_);
                        lean_del_object(v___x_4997_);
                        lean_dec(v_a_4995_);
                        v_args_5304_ = lean_ctor_get(v_value_5052_, 2);
                        v___f_5305_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2;
                        v___x_5306_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_5304_, v___f_5305_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                        if lean_obj_tag(v___x_5306_) == 0 {
                            v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
                            lean_inc(v_a_5307_);
                            lean_dec_ref_known(v___x_5306_, 1);
                            v_fst_5308_ = lean_ctor_get(v_a_5307_, 0);
                            v_snd_5309_ = lean_ctor_get(v_a_5307_, 1);
                            v_isSharedCheck_5349_ = (!lean_is_exclusive(v_a_5307_)) as u8;
                            if v_isSharedCheck_5349_ == 0 {
                                v___x_5311_ = v_a_5307_;
                                v_isShared_5312_ = v_isSharedCheck_5349_;
                                state = 53;
                                continue;
                            } else {
                                lean_inc(v_snd_5309_);
                                lean_inc(v_fst_5308_);
                                lean_dec(v_a_5307_);
                                v___x_5311_ = lean_box(0);
                                v_isShared_5312_ = v_isSharedCheck_5349_;
                                state = 53;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5018_);
                            lean_dec(v_a_5013_);
                            lean_dec_ref(v_code_4973_);
                            v_a_5350_ = lean_ctor_get(v___x_5306_, 0);
                            v_isSharedCheck_5357_ = (!lean_is_exclusive(v___x_5306_)) as u8;
                            if v_isSharedCheck_5357_ == 0 {
                                v___x_5352_ = v___x_5306_;
                                v_isShared_5353_ = v_isSharedCheck_5357_;
                                state = 61;
                                continue;
                            } else {
                                lean_inc(v_a_5350_);
                                lean_dec(v___x_5306_);
                                v___x_5352_ = lean_box(0);
                                v_isShared_5353_ = v_isSharedCheck_5357_;
                                state = 61;
                                continue;
                            }
                        }
                    }
                    13 => {
                        lean_del_object(v___x_5020_);
                        lean_dec(v_a_5018_);
                        lean_del_object(v___x_5015_);
                        lean_dec(v_a_5013_);
                        lean_del_object(v___x_4997_);
                        lean_dec(v_a_4995_);
                        lean_dec_ref(v_code_4973_);
                        v___x_5358_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
                        v___x_5359_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_5358_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                        return v___x_5359_;
                    }
                    14 => {
                        lean_del_object(v___x_5020_);
                        lean_dec(v_a_5018_);
                        lean_del_object(v___x_5015_);
                        lean_dec(v_a_5013_);
                        lean_del_object(v___x_4997_);
                        lean_dec(v_a_4995_);
                        lean_dec_ref(v_code_4973_);
                        v___y_4984_ = v_a_4976_;
                        v___y_4985_ = v_a_4977_;
                        v___y_4986_ = v_a_4978_;
                        v___y_4987_ = v_a_4979_;
                        v___y_4988_ = v_a_4980_;
                        v___y_4989_ = v_a_4981_;
                        state = 1;
                        continue;
                    }
                    15 => {
                        lean_del_object(v___x_5020_);
                        lean_dec(v_a_5018_);
                        lean_del_object(v___x_5015_);
                        lean_dec(v_a_5013_);
                        lean_del_object(v___x_4997_);
                        lean_dec(v_a_4995_);
                        lean_dec_ref(v_code_4973_);
                        v___y_4984_ = v_a_4976_;
                        v___y_4985_ = v_a_4977_;
                        v___y_4986_ = v_a_4978_;
                        v___y_4987_ = v_a_4979_;
                        v___y_4988_ = v_a_4980_;
                        v___y_4989_ = v_a_4981_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        lean_inc(v_value_5052_);
                        lean_del_object(v___x_5020_);
                        lean_del_object(v___x_5015_);
                        lean_del_object(v___x_4997_);
                        v___x_5360_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_4999_, v_a_5013_, v_a_4995_, v_value_5052_, v_a_4979_);
                        if lean_obj_tag(v___x_5360_) == 0 {
                            v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
                            v_isSharedCheck_5385_ = (!lean_is_exclusive(v___x_5360_)) as u8;
                            if v_isSharedCheck_5385_ == 0 {
                                v___x_5363_ = v___x_5360_;
                                v_isShared_5364_ = v_isSharedCheck_5385_;
                                state = 63;
                                continue;
                            } else {
                                lean_inc(v_a_5361_);
                                lean_dec(v___x_5360_);
                                v___x_5363_ = lean_box(0);
                                v_isShared_5364_ = v_isSharedCheck_5385_;
                                state = 63;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5018_);
                            lean_dec_ref(v_code_4973_);
                            v_a_5386_ = lean_ctor_get(v___x_5360_, 0);
                            v_isSharedCheck_5393_ = (!lean_is_exclusive(v___x_5360_)) as u8;
                            if v_isSharedCheck_5393_ == 0 {
                                v___x_5388_ = v___x_5360_;
                                v_isShared_5389_ = v_isSharedCheck_5393_;
                                state = 67;
                                continue;
                            } else {
                                lean_inc(v_a_5386_);
                                lean_dec(v___x_5360_);
                                v___x_5388_ = lean_box(0);
                                v_isShared_5389_ = v_isSharedCheck_5393_;
                                state = 67;
                                continue;
                            }
                        }
                    }
                }
            }
            8 => {
                if v___y_5025_ == 0 {
                    lean_dec_ref(v_code_4973_);
                    v___x_5026_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5026_, 0, v___y_5024_);
                    lean_ctor_set(v___x_5026_, 1, v_a_5018_);
                    v___y_5008_ = v___y_5023_;
                    v___y_5009_ = v___x_5026_;
                    state = 5;
                    continue;
                } else {
                    lean_dec_ref(v___y_5024_);
                    lean_dec(v_a_5018_);
                    v___y_5008_ = v___y_5023_;
                    v___y_5009_ = v_code_4973_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                if v___y_5030_ == 0 {
                    lean_dec_ref(v_code_4973_);
                    v___x_5031_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5031_, 0, v___y_5029_);
                    lean_ctor_set(v___x_5031_, 1, v_a_5018_);
                    v___y_5001_ = v___y_5028_;
                    v___y_5002_ = v___x_5031_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v___y_5029_);
                    lean_dec(v_a_5018_);
                    v___y_5001_ = v___y_5028_;
                    v___y_5002_ = v_code_4973_;
                    state = 3;
                    continue;
                }
            }
            10 => {
                if v___y_5034_ == 0 {
                    lean_dec_ref(v_code_4973_);
                    v___x_5035_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5035_, 0, v___y_5033_);
                    lean_ctor_set(v___x_5035_, 1, v_a_5018_);
                    if v_isShared_5021_ == 0 {
                        lean_ctor_set(v___x_5020_, 0, v___x_5035_);
                        v___x_5037_ = v___x_5020_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5035_);
                        v___x_5037_ = v_reuseFailAlloc_5038_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_5033_);
                    lean_dec(v_a_5018_);
                    if v_isShared_5021_ == 0 {
                        lean_ctor_set(v___x_5020_, 0, v_code_4973_);
                        v___x_5040_ = v___x_5020_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_code_4973_);
                        v___x_5040_ = v_reuseFailAlloc_5041_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_5037_;
            }
            12 => {
                return v___x_5040_;
            }
            13 => {
                if v___y_5044_ == 0 {
                    lean_dec_ref(v_code_4973_);
                    v___x_5045_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5045_, 0, v___y_5043_);
                    lean_ctor_set(v___x_5045_, 1, v_a_5018_);
                    if v_isShared_5016_ == 0 {
                        lean_ctor_set(v___x_5015_, 0, v___x_5045_);
                        v___x_5047_ = v___x_5015_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5045_);
                        v___x_5047_ = v_reuseFailAlloc_5048_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_5043_);
                    lean_dec(v_a_5018_);
                    if v_isShared_5016_ == 0 {
                        lean_ctor_set(v___x_5015_, 0, v_code_4973_);
                        v___x_5050_ = v___x_5015_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_code_4973_);
                        v___x_5050_ = v_reuseFailAlloc_5051_;
                        state = 15;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_5047_;
            }
            15 => {
                return v___x_5050_;
            }
            16 => {
                v___x_5055_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_4999_, v_a_5013_, v_a_4995_, v_value_5052_, v___y_5054_);
                if lean_obj_tag(v___x_5055_) == 0 {
                    if lean_obj_tag(v_code_4973_) == 0 {
                        v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
                        lean_inc(v_a_5056_);
                        lean_dec_ref_known(v___x_5055_, 1);
                        v_decl_5057_ = lean_ctor_get(v_code_4973_, 0);
                        v_k_5058_ = lean_ctor_get(v_code_4973_, 1);
                        v___x_5059_ = lean_ptr_addr(v_k_5058_);
                        v___x_5060_ = lean_ptr_addr(v_a_5018_);
                        v___x_5061_ = lean_usize_dec_eq(v___x_5059_, v___x_5060_);
                        if v___x_5061_ == 0 {
                            v___y_5043_ = v_a_5056_;
                            v___y_5044_ = v___x_5061_;
                            state = 13;
                            continue;
                        } else {
                            v___x_5062_ = lean_ptr_addr(v_decl_5057_);
                            v___x_5063_ = lean_ptr_addr(v_a_5056_);
                            v___x_5064_ = lean_usize_dec_eq(v___x_5062_, v___x_5063_);
                            v___y_5043_ = v_a_5056_;
                            v___y_5044_ = v___x_5064_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5018_);
                        lean_del_object(v___x_5015_);
                        lean_dec_ref(v_code_4973_);
                        v_isSharedCheck_5073_ = (!lean_is_exclusive(v___x_5055_)) as u8;
                        if v_isSharedCheck_5073_ == 0 {
                            v_unused_5074_ = lean_ctor_get(v___x_5055_, 0);
                            lean_dec(v_unused_5074_);
                            v___x_5066_ = v___x_5055_;
                            v_isShared_5067_ = v_isSharedCheck_5073_;
                            state = 17;
                            continue;
                        } else {
                            lean_dec(v___x_5055_);
                            v___x_5066_ = lean_box(0);
                            v_isShared_5067_ = v_isSharedCheck_5073_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5018_);
                    lean_del_object(v___x_5015_);
                    lean_dec_ref(v_code_4973_);
                    v_a_5075_ = lean_ctor_get(v___x_5055_, 0);
                    v_isSharedCheck_5082_ = (!lean_is_exclusive(v___x_5055_)) as u8;
                    if v_isSharedCheck_5082_ == 0 {
                        v___x_5077_ = v___x_5055_;
                        v_isShared_5078_ = v_isSharedCheck_5082_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_5075_);
                        lean_dec(v___x_5055_);
                        v___x_5077_ = lean_box(0);
                        v_isShared_5078_ = v_isSharedCheck_5082_;
                        state = 19;
                        continue;
                    }
                }
            }
            17 => {
                v___x_5068_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
                v___x_5069_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_5068_);
                if v_isShared_5067_ == 0 {
                    lean_ctor_set(v___x_5066_, 0, v___x_5069_);
                    v___x_5071_ = v___x_5066_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5069_);
                    v___x_5071_ = v_reuseFailAlloc_5072_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5071_;
            }
            19 => {
                if v_isShared_5078_ == 0 {
                    v___x_5080_ = v___x_5077_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
                    v___x_5080_ = v_reuseFailAlloc_5081_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5080_;
            }
            21 => {
                v___x_5097_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4999_, v_snd_5088_, v_a_5093_);
                lean_dec(v_snd_5088_);
                if v_isShared_5096_ == 0 {
                    lean_ctor_set(v___x_5095_, 0, v___x_5097_);
                    v___x_5099_ = v___x_5095_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5097_);
                    v___x_5099_ = v_reuseFailAlloc_5100_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5099_;
            }
            23 => {
                if v_isShared_5105_ == 0 {
                    v___x_5107_ = v___x_5104_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5108_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_a_5102_);
                    v___x_5107_ = v_reuseFailAlloc_5108_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5107_;
            }
            25 => {
                if v_isShared_5113_ == 0 {
                    v___x_5115_ = v___x_5112_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
                    v___x_5115_ = v_reuseFailAlloc_5116_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5115_;
            }
            27 => {
                if v___y_5122_ == 0 {
                    lean_del_object(v___x_5020_);
                    lean_dec(v_a_4995_);
                    v___x_5123_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_5119_, v___f_5120_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                    if lean_obj_tag(v___x_5123_) == 0 {
                        v_a_5124_ = lean_ctor_get(v___x_5123_, 0);
                        lean_inc(v_a_5124_);
                        lean_dec_ref_known(v___x_5123_, 1);
                        v_fst_5125_ = lean_ctor_get(v_a_5124_, 0);
                        lean_inc(v_fst_5125_);
                        v_snd_5126_ = lean_ctor_get(v_a_5124_, 1);
                        lean_inc(v_snd_5126_);
                        lean_dec(v_a_5124_);
                        lean_inc_ref(v_value_5052_);
                        v___x_5127_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_4999_, v_value_5052_, v_fst_5125_);
                        v___x_5128_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                            v___x_4999_,
                            v_a_5013_,
                            v___x_5127_,
                            v_a_4979_,
                        );
                        if lean_obj_tag(v___x_5128_) == 0 {
                            if lean_obj_tag(v_code_4973_) == 0 {
                                v_a_5129_ = lean_ctor_get(v___x_5128_, 0);
                                lean_inc(v_a_5129_);
                                lean_dec_ref_known(v___x_5128_, 1);
                                v_decl_5130_ = lean_ctor_get(v_code_4973_, 0);
                                v_k_5131_ = lean_ctor_get(v_code_4973_, 1);
                                v___x_5132_ = lean_ptr_addr(v_k_5131_);
                                v___x_5133_ = lean_ptr_addr(v_a_5018_);
                                v___x_5134_ = lean_usize_dec_eq(v___x_5132_, v___x_5133_);
                                if v___x_5134_ == 0 {
                                    v___y_5028_ = v_snd_5126_;
                                    v___y_5029_ = v_a_5129_;
                                    v___y_5030_ = v___x_5134_;
                                    state = 9;
                                    continue;
                                } else {
                                    v___x_5135_ = lean_ptr_addr(v_decl_5130_);
                                    v___x_5136_ = lean_ptr_addr(v_a_5129_);
                                    v___x_5137_ = lean_usize_dec_eq(v___x_5135_, v___x_5136_);
                                    v___y_5028_ = v_snd_5126_;
                                    v___y_5029_ = v_a_5129_;
                                    v___y_5030_ = v___x_5137_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v___x_5128_, 1);
                                lean_dec(v_a_5018_);
                                lean_dec_ref(v_code_4973_);
                                v___x_5138_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
                                v___x_5139_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_5138_);
                                v___y_5001_ = v_snd_5126_;
                                v___y_5002_ = v___x_5139_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_snd_5126_);
                            lean_dec(v_a_5018_);
                            lean_del_object(v___x_4997_);
                            lean_dec_ref(v_code_4973_);
                            v_a_5140_ = lean_ctor_get(v___x_5128_, 0);
                            v_isSharedCheck_5147_ = (!lean_is_exclusive(v___x_5128_)) as u8;
                            if v_isSharedCheck_5147_ == 0 {
                                v___x_5142_ = v___x_5128_;
                                v_isShared_5143_ = v_isSharedCheck_5147_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_5140_);
                                lean_dec(v___x_5128_);
                                v___x_5142_ = lean_box(0);
                                v_isShared_5143_ = v_isSharedCheck_5147_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5018_);
                        lean_dec(v_a_5013_);
                        lean_del_object(v___x_4997_);
                        lean_dec_ref(v_code_4973_);
                        v_a_5148_ = lean_ctor_get(v___x_5123_, 0);
                        v_isSharedCheck_5155_ = (!lean_is_exclusive(v___x_5123_)) as u8;
                        if v_isSharedCheck_5155_ == 0 {
                            v___x_5150_ = v___x_5123_;
                            v_isShared_5151_ = v_isSharedCheck_5155_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_5148_);
                            lean_dec(v___x_5123_);
                            v___x_5150_ = lean_box(0);
                            v_isShared_5151_ = v_isSharedCheck_5155_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4997_);
                    v_cidx_5156_ = lean_ctor_get(v_i_5118_, 1);
                    v___x_5157_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(
                        v_a_4995_,
                        v_cidx_5156_,
                    );
                    lean_dec(v_a_4995_);
                    v___x_5158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5158_, 0, v___x_5157_);
                    v___x_5159_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                        v___x_4999_,
                        v_a_5013_,
                        v___x_5158_,
                        v_a_4979_,
                    );
                    if lean_obj_tag(v___x_5159_) == 0 {
                        if lean_obj_tag(v_code_4973_) == 0 {
                            v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
                            lean_inc(v_a_5160_);
                            lean_dec_ref_known(v___x_5159_, 1);
                            v_decl_5161_ = lean_ctor_get(v_code_4973_, 0);
                            v_k_5162_ = lean_ctor_get(v_code_4973_, 1);
                            v___x_5163_ = lean_ptr_addr(v_k_5162_);
                            v___x_5164_ = lean_ptr_addr(v_a_5018_);
                            v___x_5165_ = lean_usize_dec_eq(v___x_5163_, v___x_5164_);
                            if v___x_5165_ == 0 {
                                v___y_5033_ = v_a_5160_;
                                v___y_5034_ = v___x_5165_;
                                state = 10;
                                continue;
                            } else {
                                v___x_5166_ = lean_ptr_addr(v_decl_5161_);
                                v___x_5167_ = lean_ptr_addr(v_a_5160_);
                                v___x_5168_ = lean_usize_dec_eq(v___x_5166_, v___x_5167_);
                                v___y_5033_ = v_a_5160_;
                                v___y_5034_ = v___x_5168_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_5020_);
                            lean_dec(v_a_5018_);
                            lean_dec_ref(v_code_4973_);
                            v_isSharedCheck_5177_ = (!lean_is_exclusive(v___x_5159_)) as u8;
                            if v_isSharedCheck_5177_ == 0 {
                                v_unused_5178_ = lean_ctor_get(v___x_5159_, 0);
                                lean_dec(v_unused_5178_);
                                v___x_5170_ = v___x_5159_;
                                v_isShared_5171_ = v_isSharedCheck_5177_;
                                state = 32;
                                continue;
                            } else {
                                lean_dec(v___x_5159_);
                                v___x_5170_ = lean_box(0);
                                v_isShared_5171_ = v_isSharedCheck_5177_;
                                state = 32;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_5020_);
                        lean_dec(v_a_5018_);
                        lean_dec_ref(v_code_4973_);
                        v_a_5179_ = lean_ctor_get(v___x_5159_, 0);
                        v_isSharedCheck_5186_ = (!lean_is_exclusive(v___x_5159_)) as u8;
                        if v_isSharedCheck_5186_ == 0 {
                            v___x_5181_ = v___x_5159_;
                            v_isShared_5182_ = v_isSharedCheck_5186_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_a_5179_);
                            lean_dec(v___x_5159_);
                            v___x_5181_ = lean_box(0);
                            v_isShared_5182_ = v_isSharedCheck_5186_;
                            state = 34;
                            continue;
                        }
                    }
                }
            }
            28 => {
                if v_isShared_5143_ == 0 {
                    v___x_5145_ = v___x_5142_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5146_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
                    v___x_5145_ = v_reuseFailAlloc_5146_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5145_;
            }
            30 => {
                if v_isShared_5151_ == 0 {
                    v___x_5153_ = v___x_5150_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5148_);
                    v___x_5153_ = v_reuseFailAlloc_5154_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_5153_;
            }
            32 => {
                v___x_5172_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
                v___x_5173_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_5172_);
                if v_isShared_5171_ == 0 {
                    lean_ctor_set(v___x_5170_, 0, v___x_5173_);
                    v___x_5175_ = v___x_5170_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5173_);
                    v___x_5175_ = v_reuseFailAlloc_5176_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5175_;
            }
            34 => {
                if v_isShared_5182_ == 0 {
                    v___x_5184_ = v___x_5181_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
                    v___x_5184_ = v_reuseFailAlloc_5185_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_5184_;
            }
            36 => {
                v___x_5210_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4999_, v_snd_5201_, v_a_5206_);
                lean_dec(v_snd_5201_);
                if v_isShared_5209_ == 0 {
                    lean_ctor_set(v___x_5208_, 0, v___x_5210_);
                    v___x_5212_ = v___x_5208_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5213_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5210_);
                    v___x_5212_ = v_reuseFailAlloc_5213_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_5212_;
            }
            38 => {
                if v_isShared_5218_ == 0 {
                    v___x_5220_ = v___x_5217_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
                    v___x_5220_ = v_reuseFailAlloc_5221_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_5220_;
            }
            40 => {
                if v_isShared_5226_ == 0 {
                    v___x_5228_ = v___x_5225_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5229_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_a_5223_);
                    v___x_5228_ = v_reuseFailAlloc_5229_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5228_;
            }
            42 => {
                if v_isShared_5236_ == 0 {
                    v___x_5238_ = v___x_5235_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
                    v___x_5238_ = v_reuseFailAlloc_5239_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_5238_;
            }
            44 => {
                v___x_5251_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_5242_, v___f_5248_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
                if lean_obj_tag(v___x_5251_) == 0 {
                    v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
                    lean_inc(v_a_5252_);
                    lean_dec_ref_known(v___x_5251_, 1);
                    v_fst_5253_ = lean_ctor_get(v_a_5252_, 0);
                    lean_inc(v_fst_5253_);
                    v_snd_5254_ = lean_ctor_get(v_a_5252_, 1);
                    lean_inc(v_snd_5254_);
                    lean_dec(v_a_5252_);
                    v___x_5255_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp(v___x_4999_, v_value_5052_, v___y_5250_, v_fst_5253_);
                    v___x_5256_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                        v___x_4999_,
                        v_a_5013_,
                        v___x_5255_,
                        v_a_4979_,
                    );
                    if lean_obj_tag(v___x_5256_) == 0 {
                        if lean_obj_tag(v_code_4973_) == 0 {
                            v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
                            lean_inc(v_a_5257_);
                            lean_dec_ref_known(v___x_5256_, 1);
                            v_decl_5258_ = lean_ctor_get(v_code_4973_, 0);
                            v_k_5259_ = lean_ctor_get(v_code_4973_, 1);
                            v___x_5260_ = lean_ptr_addr(v_k_5259_);
                            v___x_5261_ = lean_ptr_addr(v_a_5018_);
                            v___x_5262_ = lean_usize_dec_eq(v___x_5260_, v___x_5261_);
                            if v___x_5262_ == 0 {
                                v___y_5023_ = v_snd_5254_;
                                v___y_5024_ = v_a_5257_;
                                v___y_5025_ = v___x_5262_;
                                state = 8;
                                continue;
                            } else {
                                v___x_5263_ = lean_ptr_addr(v_decl_5258_);
                                v___x_5264_ = lean_ptr_addr(v_a_5257_);
                                v___x_5265_ = lean_usize_dec_eq(v___x_5263_, v___x_5264_);
                                v___y_5023_ = v_snd_5254_;
                                v___y_5024_ = v_a_5257_;
                                v___y_5025_ = v___x_5265_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v___x_5256_, 1);
                            lean_dec(v_a_5018_);
                            lean_dec_ref(v_code_4973_);
                            v___x_5266_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
                            v___x_5267_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_5266_);
                            v___y_5008_ = v_snd_5254_;
                            v___y_5009_ = v___x_5267_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_5254_);
                        lean_dec(v_a_5018_);
                        lean_dec_ref(v_code_4973_);
                        v_a_5268_ = lean_ctor_get(v___x_5256_, 0);
                        v_isSharedCheck_5275_ = (!lean_is_exclusive(v___x_5256_)) as u8;
                        if v_isSharedCheck_5275_ == 0 {
                            v___x_5270_ = v___x_5256_;
                            v_isShared_5271_ = v_isSharedCheck_5275_;
                            state = 45;
                            continue;
                        } else {
                            lean_inc(v_a_5268_);
                            lean_dec(v___x_5256_);
                            v___x_5270_ = lean_box(0);
                            v_isShared_5271_ = v_isSharedCheck_5275_;
                            state = 45;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_5250_);
                    lean_dec(v_a_5018_);
                    lean_dec(v_a_5013_);
                    lean_dec_ref(v_code_4973_);
                    v_a_5276_ = lean_ctor_get(v___x_5251_, 0);
                    v_isSharedCheck_5283_ = (!lean_is_exclusive(v___x_5251_)) as u8;
                    if v_isSharedCheck_5283_ == 0 {
                        v___x_5278_ = v___x_5251_;
                        v_isShared_5279_ = v_isSharedCheck_5283_;
                        state = 47;
                        continue;
                    } else {
                        lean_inc(v_a_5276_);
                        lean_dec(v___x_5251_);
                        v___x_5278_ = lean_box(0);
                        v_isShared_5279_ = v_isSharedCheck_5283_;
                        state = 47;
                        continue;
                    }
                }
            }
            45 => {
                if v_isShared_5271_ == 0 {
                    v___x_5273_ = v___x_5270_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
                    v___x_5273_ = v_reuseFailAlloc_5274_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_5273_;
            }
            47 => {
                if v_isShared_5279_ == 0 {
                    v___x_5281_ = v___x_5278_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_5281_;
            }
            49 => {
                if v_isShared_5289_ == 0 {
                    v___x_5291_ = v___x_5288_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
                    v___x_5291_ = v_reuseFailAlloc_5292_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_5291_;
            }
            51 => {
                if v_isShared_5299_ == 0 {
                    v___x_5301_ = v___x_5298_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
                    v___x_5301_ = v_reuseFailAlloc_5302_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5301_;
            }
            53 => {
                lean_inc_ref(v_value_5052_);
                v___x_5313_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_4999_, v_value_5052_, v_fst_5308_);
                v___x_5314_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                    v___x_4999_,
                    v_a_5013_,
                    v___x_5313_,
                    v_a_4979_,
                );
                if lean_obj_tag(v___x_5314_) == 0 {
                    v_a_5315_ = lean_ctor_get(v___x_5314_, 0);
                    v_isSharedCheck_5340_ = (!lean_is_exclusive(v___x_5314_)) as u8;
                    if v_isSharedCheck_5340_ == 0 {
                        v___x_5317_ = v___x_5314_;
                        v_isShared_5318_ = v_isSharedCheck_5340_;
                        state = 54;
                        continue;
                    } else {
                        lean_inc(v_a_5315_);
                        lean_dec(v___x_5314_);
                        v___x_5317_ = lean_box(0);
                        v_isShared_5318_ = v_isSharedCheck_5340_;
                        state = 54;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5311_);
                    lean_dec(v_snd_5309_);
                    lean_dec(v_a_5018_);
                    lean_dec_ref(v_code_4973_);
                    v_a_5341_ = lean_ctor_get(v___x_5314_, 0);
                    v_isSharedCheck_5348_ = (!lean_is_exclusive(v___x_5314_)) as u8;
                    if v_isSharedCheck_5348_ == 0 {
                        v___x_5343_ = v___x_5314_;
                        v_isShared_5344_ = v_isSharedCheck_5348_;
                        state = 59;
                        continue;
                    } else {
                        lean_inc(v_a_5341_);
                        lean_dec(v___x_5314_);
                        v___x_5343_ = lean_box(0);
                        v_isShared_5344_ = v_isSharedCheck_5348_;
                        state = 59;
                        continue;
                    }
                }
            }
            54 => {
                if lean_obj_tag(v_code_4973_) == 0 {
                    v_decl_5330_ = lean_ctor_get(v_code_4973_, 0);
                    v_k_5331_ = lean_ctor_get(v_code_4973_, 1);
                    v___x_5332_ = lean_ptr_addr(v_k_5331_);
                    v___x_5333_ = lean_ptr_addr(v_a_5018_);
                    v___x_5334_ = lean_usize_dec_eq(v___x_5332_, v___x_5333_);
                    if v___x_5334_ == 0 {
                        v___y_5326_ = v___x_5334_;
                        state = 57;
                        continue;
                    } else {
                        v___x_5335_ = lean_ptr_addr(v_decl_5330_);
                        v___x_5336_ = lean_ptr_addr(v_a_5315_);
                        v___x_5337_ = lean_usize_dec_eq(v___x_5335_, v___x_5336_);
                        v___y_5326_ = v___x_5337_;
                        state = 57;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5315_);
                    lean_del_object(v___x_5311_);
                    lean_dec(v_a_5018_);
                    lean_dec_ref(v_code_4973_);
                    v___x_5338_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
                    v___x_5339_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_5338_);
                    v___y_5320_ = v___x_5339_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                v___x_5321_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4999_, v_snd_5309_, v___y_5320_);
                lean_dec(v_snd_5309_);
                if v_isShared_5318_ == 0 {
                    lean_ctor_set(v___x_5317_, 0, v___x_5321_);
                    v___x_5323_ = v___x_5317_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5324_, 0, v___x_5321_);
                    v___x_5323_ = v_reuseFailAlloc_5324_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_5323_;
            }
            57 => {
                if v___y_5326_ == 0 {
                    lean_dec_ref(v_code_4973_);
                    if v_isShared_5312_ == 0 {
                        lean_ctor_set(v___x_5311_, 1, v_a_5018_);
                        lean_ctor_set(v___x_5311_, 0, v_a_5315_);
                        v___x_5328_ = v___x_5311_;
                        state = 58;
                        continue;
                    } else {
                        v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5315_);
                        lean_ctor_set(v_reuseFailAlloc_5329_, 1, v_a_5018_);
                        v___x_5328_ = v_reuseFailAlloc_5329_;
                        state = 58;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5315_);
                    lean_del_object(v___x_5311_);
                    lean_dec(v_a_5018_);
                    v___y_5320_ = v_code_4973_;
                    state = 55;
                    continue;
                }
            }
            58 => {
                v___y_5320_ = v___x_5328_;
                state = 55;
                continue;
            }
            59 => {
                if v_isShared_5344_ == 0 {
                    v___x_5346_ = v___x_5343_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_5347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_a_5341_);
                    v___x_5346_ = v_reuseFailAlloc_5347_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_5346_;
            }
            61 => {
                if v_isShared_5353_ == 0 {
                    v___x_5355_ = v___x_5352_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_5356_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5350_);
                    v___x_5355_ = v_reuseFailAlloc_5356_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_5355_;
            }
            63 => {
                if lean_obj_tag(v_code_4973_) == 0 {
                    v_decl_5374_ = lean_ctor_get(v_code_4973_, 0);
                    v_k_5375_ = lean_ctor_get(v_code_4973_, 1);
                    v___x_5376_ = lean_ptr_addr(v_k_5375_);
                    v___x_5377_ = lean_ptr_addr(v_a_5018_);
                    v___x_5378_ = lean_usize_dec_eq(v___x_5376_, v___x_5377_);
                    if v___x_5378_ == 0 {
                        v___y_5366_ = v___x_5378_;
                        state = 64;
                        continue;
                    } else {
                        v___x_5379_ = lean_ptr_addr(v_decl_5374_);
                        v___x_5380_ = lean_ptr_addr(v_a_5361_);
                        v___x_5381_ = lean_usize_dec_eq(v___x_5379_, v___x_5380_);
                        v___y_5366_ = v___x_5381_;
                        state = 64;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5363_);
                    lean_dec(v_a_5361_);
                    lean_dec(v_a_5018_);
                    lean_dec_ref(v_code_4973_);
                    v___x_5382_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
                    v___x_5383_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_5382_);
                    v___x_5384_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5384_, 0, v___x_5383_);
                    return v___x_5384_;
                }
            }
            64 => {
                if v___y_5366_ == 0 {
                    lean_dec_ref(v_code_4973_);
                    v___x_5367_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5367_, 0, v_a_5361_);
                    lean_ctor_set(v___x_5367_, 1, v_a_5018_);
                    if v_isShared_5364_ == 0 {
                        lean_ctor_set(v___x_5363_, 0, v___x_5367_);
                        v___x_5369_ = v___x_5363_;
                        state = 65;
                        continue;
                    } else {
                        v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5367_);
                        v___x_5369_ = v_reuseFailAlloc_5370_;
                        state = 65;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5361_);
                    lean_dec(v_a_5018_);
                    if v_isShared_5364_ == 0 {
                        lean_ctor_set(v___x_5363_, 0, v_code_4973_);
                        v___x_5372_ = v___x_5363_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_code_4973_);
                        v___x_5372_ = v_reuseFailAlloc_5373_;
                        state = 66;
                        continue;
                    }
                }
            }
            65 => {
                return v___x_5369_;
            }
            66 => {
                return v___x_5372_;
            }
            67 => {
                if v_isShared_5389_ == 0 {
                    v___x_5391_ = v___x_5388_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_5392_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_a_5386_);
                    v___x_5391_ = v_reuseFailAlloc_5392_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_5391_;
            }
            69 => {
                if v_isShared_5399_ == 0 {
                    v___x_5401_ = v___x_5398_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_5402_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
                    v___x_5401_ = v_reuseFailAlloc_5402_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_5401_;
            }
            71 => {
                if v_isShared_5408_ == 0 {
                    v___x_5410_ = v___x_5407_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_5411_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_a_5405_);
                    v___x_5410_ = v_reuseFailAlloc_5411_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_5410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1()
-> *mut LeanObject {
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    v___x_5414_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2;
    v___x_5415_ = lean_unsigned_to_nat(44);
    v___x_5416_ = lean_unsigned_to_nat(284);
    v___x_5417_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0;
    v___x_5418_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0;
    v___x_5419_ = l_mkPanicMessageWithDecl(
        v___x_5418_,
        v___x_5417_,
        v___x_5416_,
        v___x_5415_,
        v___x_5414_,
    );
    return v___x_5419_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2()
-> *mut LeanObject {
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    v___x_5420_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2;
    v___x_5421_ = lean_unsigned_to_nat(59);
    v___x_5422_ = lean_unsigned_to_nat(287);
    v___x_5423_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0;
    v___x_5424_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0;
    v___x_5425_ = l_mkPanicMessageWithDecl(
        v___x_5424_,
        v___x_5423_,
        v___x_5422_,
        v___x_5421_,
        v___x_5420_,
    );
    return v___x_5425_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(
    mut v_code_5426_: *mut LeanObject,
    mut v_a_5427_: *mut LeanObject,
    mut v_a_5428_: *mut LeanObject,
    mut v_a_5429_: *mut LeanObject,
    mut v_a_5430_: *mut LeanObject,
    mut v_a_5431_: *mut LeanObject,
    mut v_a_5432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currDeclResultType_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: u8 = 0;
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5451_: u8 = 0;
    let mut v___y_5453_: u8 = 0;
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5456_: u8 = 0;
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5463_: u8 = 0;
    let mut v_unused_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: usize = 0;
    let mut v___x_5470_: usize = 0;
    let mut v___x_5471_: u8 = 0;
    let mut v___x_5472_: usize = 0;
    let mut v___x_5473_: usize = 0;
    let mut v___x_5474_: u8 = 0;
    let mut v_isSharedCheck_5475_: u8 = 0;
    let mut v_a_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5479_: u8 = 0;
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5483_: u8 = 0;
    let mut v_fvarId_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: u8 = 0;
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5497_: u8 = 0;
    let mut v_fst_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5507_: u8 = 0;
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5514_: u8 = 0;
    let mut v_unused_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: u8 = 0;
    let mut v___x_5518_: usize = 0;
    let mut v___x_5519_: usize = 0;
    let mut v___x_5520_: u8 = 0;
    let mut v_isSharedCheck_5521_: u8 = 0;
    let mut v_a_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5525_: u8 = 0;
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5529_: u8 = 0;
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5539_: u8 = 0;
    let mut v_cases_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: u8 = 0;
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: u8 = 0;
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5564_: u8 = 0;
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5569_: u8 = 0;
    let mut v_a_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5573_: u8 = 0;
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5577_: u8 = 0;
    let mut v_a_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5581_: u8 = 0;
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5585_: u8 = 0;
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5590_: u8 = 0;
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5594_: u8 = 0;
    let mut v_a_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v_fvarId_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currDeclResultType_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: u8 = 0;
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: u8 = 0;
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5619_: u8 = 0;
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5624_: u8 = 0;
    let mut v_a_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5632_: u8 = 0;
    let mut v_a_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5636_: u8 = 0;
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5640_: u8 = 0;
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5645_: u8 = 0;
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5649_: u8 = 0;
    let mut v_type_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currDeclResultType_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: usize = 0;
    let mut v___x_5653_: usize = 0;
    let mut v___x_5654_: u8 = 0;
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5657_: u8 = 0;
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5662_: u8 = 0;
    let mut v_unused_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: u8 = 0;
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: u8 = 0;
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5686_: u8 = 0;
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5691_: u8 = 0;
    let mut v_a_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5695_: u8 = 0;
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5699_: u8 = 0;
    let mut v_a_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5703_: u8 = 0;
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5707_: u8 = 0;
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5712_: u8 = 0;
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5716_: u8 = 0;
    let mut v_fvarId_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: u8 = 0;
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: u8 = 0;
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5739_: u8 = 0;
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5744_: u8 = 0;
    let mut v_a_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5748_: u8 = 0;
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5752_: u8 = 0;
    let mut v_a_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5760_: u8 = 0;
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5765_: u8 = 0;
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5769_: u8 = 0;
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_5426_) {
                0 => {
                    v_decl_5434_ = lean_ctor_get(v_code_5426_, 0);
                    lean_inc_ref(v_decl_5434_);
                    v_k_5435_ = lean_ctor_get(v_code_5426_, 1);
                    lean_inc_ref(v_k_5435_);
                    v___x_5436_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_5426_, v_decl_5434_, v_k_5435_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                    return v___x_5436_;
                }
                2 => {
                    v_decl_5437_ = lean_ctor_get(v_code_5426_, 0);
                    v_k_5438_ = lean_ctor_get(v_code_5426_, 1);
                    v_params_5439_ = lean_ctor_get(v_decl_5437_, 2);
                    v_value_5440_ = lean_ctor_get(v_decl_5437_, 4);
                    lean_inc_ref(v_value_5440_);
                    v___x_5441_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_value_5440_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                    if lean_obj_tag(v___x_5441_) == 0 {
                        v_a_5442_ = lean_ctor_get(v___x_5441_, 0);
                        lean_inc(v_a_5442_);
                        lean_dec_ref_known(v___x_5441_, 1);
                        v_currDeclResultType_5443_ = lean_ctor_get(v_a_5427_, 1);
                        v___x_5444_ = 1;
                        lean_inc_ref(v_params_5439_);
                        lean_inc_ref(v_currDeclResultType_5443_);
                        lean_inc_ref(v_decl_5437_);
                        v___x_5445_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5444_, v_decl_5437_, v_currDeclResultType_5443_, v_params_5439_, v_a_5442_, v_a_5430_);
                        if lean_obj_tag(v___x_5445_) == 0 {
                            v_a_5446_ = lean_ctor_get(v___x_5445_, 0);
                            lean_inc(v_a_5446_);
                            lean_dec_ref_known(v___x_5445_, 1);
                            lean_inc_ref(v_k_5438_);
                            v___x_5447_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_5438_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                            if lean_obj_tag(v___x_5447_) == 0 {
                                v_a_5448_ = lean_ctor_get(v___x_5447_, 0);
                                v_isSharedCheck_5475_ = (!lean_is_exclusive(v___x_5447_)) as u8;
                                if v_isSharedCheck_5475_ == 0 {
                                    v___x_5450_ = v___x_5447_;
                                    v_isShared_5451_ = v_isSharedCheck_5475_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_5448_);
                                    lean_dec(v___x_5447_);
                                    v___x_5450_ = lean_box(0);
                                    v_isShared_5451_ = v_isSharedCheck_5475_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5446_);
                                lean_dec_ref_known(v_code_5426_, 2);
                                return v___x_5447_;
                            }
                        } else {
                            lean_dec_ref_known(v_code_5426_, 2);
                            v_a_5476_ = lean_ctor_get(v___x_5445_, 0);
                            v_isSharedCheck_5483_ = (!lean_is_exclusive(v___x_5445_)) as u8;
                            if v_isSharedCheck_5483_ == 0 {
                                v___x_5478_ = v___x_5445_;
                                v_isShared_5479_ = v_isSharedCheck_5483_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_5476_);
                                lean_dec(v___x_5445_);
                                v___x_5478_ = lean_box(0);
                                v_isShared_5479_ = v_isSharedCheck_5483_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_5426_, 2);
                        return v___x_5441_;
                    }
                }
                3 => {
                    v_fvarId_5484_ = lean_ctor_get(v_code_5426_, 0);
                    v_args_5485_ = lean_ctor_get(v_code_5426_, 1);
                    v___x_5486_ = 1;
                    v___x_5487_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
                        v___x_5486_,
                        v_fvarId_5484_,
                        v_a_5430_,
                    );
                    if lean_obj_tag(v___x_5487_) == 0 {
                        v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
                        lean_inc(v_a_5488_);
                        lean_dec_ref_known(v___x_5487_, 1);
                        if lean_obj_tag(v_a_5488_) == 1 {
                            v_val_5489_ = lean_ctor_get(v_a_5488_, 0);
                            lean_inc(v_val_5489_);
                            lean_dec_ref_known(v_a_5488_, 1);
                            v_params_5490_ = lean_ctor_get(v_val_5489_, 2);
                            lean_inc_ref(v_params_5490_);
                            lean_dec(v_val_5489_);
                            v___x_5491_ = lean_box((v___x_5486_) as usize);
                            v___f_5492_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                            lean_closure_set(v___f_5492_, 0, v___x_5491_);
                            lean_closure_set(v___f_5492_, 1, v_params_5490_);
                            v___x_5493_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_5485_, v___f_5492_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                            if lean_obj_tag(v___x_5493_) == 0 {
                                v_a_5494_ = lean_ctor_get(v___x_5493_, 0);
                                v_isSharedCheck_5521_ = (!lean_is_exclusive(v___x_5493_)) as u8;
                                if v_isSharedCheck_5521_ == 0 {
                                    v___x_5496_ = v___x_5493_;
                                    v_isShared_5497_ = v_isSharedCheck_5521_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_5494_);
                                    lean_dec(v___x_5493_);
                                    v___x_5496_ = lean_box(0);
                                    v_isShared_5497_ = v_isSharedCheck_5521_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_code_5426_, 2);
                                v_a_5522_ = lean_ctor_get(v___x_5493_, 0);
                                v_isSharedCheck_5529_ = (!lean_is_exclusive(v___x_5493_)) as u8;
                                if v_isSharedCheck_5529_ == 0 {
                                    v___x_5524_ = v___x_5493_;
                                    v_isShared_5525_ = v_isSharedCheck_5529_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_5522_);
                                    lean_dec(v___x_5493_);
                                    v___x_5524_ = lean_box(0);
                                    v_isShared_5525_ = v_isSharedCheck_5529_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5488_);
                            lean_dec_ref_known(v_code_5426_, 2);
                            v___x_5530_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1);
                            v___x_5531_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_5530_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                            return v___x_5531_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_5426_, 2);
                        v_a_5532_ = lean_ctor_get(v___x_5487_, 0);
                        v_isSharedCheck_5539_ = (!lean_is_exclusive(v___x_5487_)) as u8;
                        if v_isSharedCheck_5539_ == 0 {
                            v___x_5534_ = v___x_5487_;
                            v_isShared_5535_ = v_isSharedCheck_5539_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_5532_);
                            lean_dec(v___x_5487_);
                            v___x_5534_ = lean_box(0);
                            v_isShared_5535_ = v_isSharedCheck_5539_;
                            state = 17;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_5540_ = lean_ctor_get(v_code_5426_, 0);
                    v_typeName_5541_ = lean_ctor_get(v_cases_5540_, 0);
                    lean_inc(v_typeName_5541_);
                    v_resultType_5542_ = lean_ctor_get(v_cases_5540_, 1);
                    lean_inc_ref(v_resultType_5542_);
                    v_discr_5543_ = lean_ctor_get(v_cases_5540_, 2);
                    lean_inc(v_discr_5543_);
                    v_alts_5544_ = lean_ctor_get(v_cases_5540_, 3);
                    lean_inc_ref_n(v_alts_5544_, 2);
                    v___x_5545_ = lean_unsigned_to_nat(0);
                    v___x_5546_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v___x_5545_, v_alts_5544_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                    if lean_obj_tag(v___x_5546_) == 0 {
                        v_a_5547_ = lean_ctor_get(v___x_5546_, 0);
                        lean_inc(v_a_5547_);
                        lean_dec_ref_known(v___x_5546_, 1);
                        lean_inc(v_discr_5543_);
                        v___x_5548_ = l_Lean_Compiler_LCNF_getType(
                            v_discr_5543_,
                            v_a_5429_,
                            v_a_5430_,
                            v_a_5431_,
                            v_a_5432_,
                        );
                        if lean_obj_tag(v___x_5548_) == 0 {
                            v_a_5549_ = lean_ctor_get(v___x_5548_, 0);
                            lean_inc(v_a_5549_);
                            lean_dec_ref_known(v___x_5548_, 1);
                            v___x_5550_ = lean_box(0);
                            lean_inc(v_typeName_5541_);
                            v___x_5551_ = l_Lean_mkConst(v_typeName_5541_, v___x_5550_);
                            v___x_5552_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_5549_, v___x_5551_);
                            if v___x_5552_ == 0 {
                                lean_inc_ref(v___x_5551_);
                                lean_inc(v_discr_5543_);
                                v___x_5553_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_discr_5543_, v_a_5549_, v___x_5551_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                if lean_obj_tag(v___x_5553_) == 0 {
                                    v_a_5554_ = lean_ctor_get(v___x_5553_, 0);
                                    lean_inc(v_a_5554_);
                                    lean_dec_ref_known(v___x_5553_, 1);
                                    v___x_5555_ = 1;
                                    v___x_5556_ = lean_box(0);
                                    v___x_5557_ = l_Lean_Compiler_LCNF_mkLetDecl(
                                        v___x_5555_,
                                        v___x_5556_,
                                        v___x_5551_,
                                        v_a_5554_,
                                        v_a_5429_,
                                        v_a_5430_,
                                        v_a_5431_,
                                        v_a_5432_,
                                    );
                                    if lean_obj_tag(v___x_5557_) == 0 {
                                        v_a_5558_ = lean_ctor_get(v___x_5557_, 0);
                                        lean_inc(v_a_5558_);
                                        lean_dec_ref_known(v___x_5557_, 1);
                                        v_fvarId_5559_ = lean_ctor_get(v_a_5558_, 0);
                                        lean_inc(v_fvarId_5559_);
                                        v___x_5560_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_5541_, v_a_5547_, v_discr_5543_, v_code_5426_, v_alts_5544_, v_resultType_5542_, v_fvarId_5559_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                        lean_dec_ref(v_resultType_5542_);
                                        lean_dec_ref(v_alts_5544_);
                                        lean_dec(v_discr_5543_);
                                        if lean_obj_tag(v___x_5560_) == 0 {
                                            v_a_5561_ = lean_ctor_get(v___x_5560_, 0);
                                            v_isSharedCheck_5569_ =
                                                (!lean_is_exclusive(v___x_5560_)) as u8;
                                            if v_isSharedCheck_5569_ == 0 {
                                                v___x_5563_ = v___x_5560_;
                                                v_isShared_5564_ = v_isSharedCheck_5569_;
                                                state = 19;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5561_);
                                                lean_dec(v___x_5560_);
                                                v___x_5563_ = lean_box(0);
                                                v_isShared_5564_ = v_isSharedCheck_5569_;
                                                state = 19;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_5558_);
                                            return v___x_5560_;
                                        }
                                    } else {
                                        lean_dec(v_a_5547_);
                                        lean_dec_ref(v_alts_5544_);
                                        lean_dec(v_discr_5543_);
                                        lean_dec_ref(v_resultType_5542_);
                                        lean_dec(v_typeName_5541_);
                                        lean_dec_ref_known(v_code_5426_, 1);
                                        v_a_5570_ = lean_ctor_get(v___x_5557_, 0);
                                        v_isSharedCheck_5577_ =
                                            (!lean_is_exclusive(v___x_5557_)) as u8;
                                        if v_isSharedCheck_5577_ == 0 {
                                            v___x_5572_ = v___x_5557_;
                                            v_isShared_5573_ = v_isSharedCheck_5577_;
                                            state = 21;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5570_);
                                            lean_dec(v___x_5557_);
                                            v___x_5572_ = lean_box(0);
                                            v_isShared_5573_ = v_isSharedCheck_5577_;
                                            state = 21;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_5551_);
                                    lean_dec(v_a_5547_);
                                    lean_dec_ref(v_alts_5544_);
                                    lean_dec(v_discr_5543_);
                                    lean_dec_ref(v_resultType_5542_);
                                    lean_dec(v_typeName_5541_);
                                    lean_dec_ref_known(v_code_5426_, 1);
                                    v_a_5578_ = lean_ctor_get(v___x_5553_, 0);
                                    v_isSharedCheck_5585_ = (!lean_is_exclusive(v___x_5553_)) as u8;
                                    if v_isSharedCheck_5585_ == 0 {
                                        v___x_5580_ = v___x_5553_;
                                        v_isShared_5581_ = v_isSharedCheck_5585_;
                                        state = 23;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5578_);
                                        lean_dec(v___x_5553_);
                                        v___x_5580_ = lean_box(0);
                                        v_isShared_5581_ = v_isSharedCheck_5585_;
                                        state = 23;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_5551_);
                                lean_dec(v_a_5549_);
                                lean_inc(v_discr_5543_);
                                v___x_5586_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_5541_, v_a_5547_, v_discr_5543_, v_code_5426_, v_alts_5544_, v_resultType_5542_, v_discr_5543_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                lean_dec_ref(v_resultType_5542_);
                                lean_dec_ref(v_alts_5544_);
                                lean_dec(v_discr_5543_);
                                return v___x_5586_;
                            }
                        } else {
                            lean_dec(v_a_5547_);
                            lean_dec_ref(v_alts_5544_);
                            lean_dec(v_discr_5543_);
                            lean_dec_ref(v_resultType_5542_);
                            lean_dec(v_typeName_5541_);
                            lean_dec_ref_known(v_code_5426_, 1);
                            v_a_5587_ = lean_ctor_get(v___x_5548_, 0);
                            v_isSharedCheck_5594_ = (!lean_is_exclusive(v___x_5548_)) as u8;
                            if v_isSharedCheck_5594_ == 0 {
                                v___x_5589_ = v___x_5548_;
                                v_isShared_5590_ = v_isSharedCheck_5594_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_5587_);
                                lean_dec(v___x_5548_);
                                v___x_5589_ = lean_box(0);
                                v_isShared_5590_ = v_isSharedCheck_5594_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_alts_5544_);
                        lean_dec(v_discr_5543_);
                        lean_dec_ref(v_resultType_5542_);
                        lean_dec(v_typeName_5541_);
                        lean_dec_ref_known(v_code_5426_, 1);
                        v_a_5595_ = lean_ctor_get(v___x_5546_, 0);
                        v_isSharedCheck_5602_ = (!lean_is_exclusive(v___x_5546_)) as u8;
                        if v_isSharedCheck_5602_ == 0 {
                            v___x_5597_ = v___x_5546_;
                            v_isShared_5598_ = v_isSharedCheck_5602_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_5595_);
                            lean_dec(v___x_5546_);
                            v___x_5597_ = lean_box(0);
                            v_isShared_5598_ = v_isSharedCheck_5602_;
                            state = 27;
                            continue;
                        }
                    }
                }
                5 => {
                    v_fvarId_5603_ = lean_ctor_get(v_code_5426_, 0);
                    lean_inc_n(v_fvarId_5603_, 2);
                    v___x_5604_ = l_Lean_Compiler_LCNF_getType(
                        v_fvarId_5603_,
                        v_a_5429_,
                        v_a_5430_,
                        v_a_5431_,
                        v_a_5432_,
                    );
                    if lean_obj_tag(v___x_5604_) == 0 {
                        v_a_5605_ = lean_ctor_get(v___x_5604_, 0);
                        lean_inc(v_a_5605_);
                        lean_dec_ref_known(v___x_5604_, 1);
                        v_currDeclResultType_5606_ = lean_ctor_get(v_a_5427_, 1);
                        v___x_5607_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_5605_, v_currDeclResultType_5606_);
                        if v___x_5607_ == 0 {
                            lean_inc_ref(v_currDeclResultType_5606_);
                            lean_inc(v_fvarId_5603_);
                            v___x_5608_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_5603_, v_a_5605_, v_currDeclResultType_5606_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                            if lean_obj_tag(v___x_5608_) == 0 {
                                v_a_5609_ = lean_ctor_get(v___x_5608_, 0);
                                lean_inc(v_a_5609_);
                                lean_dec_ref_known(v___x_5608_, 1);
                                v___x_5610_ = 1;
                                v___x_5611_ = lean_box(0);
                                lean_inc_ref(v_currDeclResultType_5606_);
                                v___x_5612_ = l_Lean_Compiler_LCNF_mkLetDecl(
                                    v___x_5610_,
                                    v___x_5611_,
                                    v_currDeclResultType_5606_,
                                    v_a_5609_,
                                    v_a_5429_,
                                    v_a_5430_,
                                    v_a_5431_,
                                    v_a_5432_,
                                );
                                if lean_obj_tag(v___x_5612_) == 0 {
                                    v_a_5613_ = lean_ctor_get(v___x_5612_, 0);
                                    lean_inc(v_a_5613_);
                                    lean_dec_ref_known(v___x_5612_, 1);
                                    v_fvarId_5614_ = lean_ctor_get(v_a_5613_, 0);
                                    lean_inc(v_fvarId_5614_);
                                    v___x_5615_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_5603_, v_code_5426_, v_fvarId_5614_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                    lean_dec(v_fvarId_5603_);
                                    if lean_obj_tag(v___x_5615_) == 0 {
                                        v_a_5616_ = lean_ctor_get(v___x_5615_, 0);
                                        v_isSharedCheck_5624_ =
                                            (!lean_is_exclusive(v___x_5615_)) as u8;
                                        if v_isSharedCheck_5624_ == 0 {
                                            v___x_5618_ = v___x_5615_;
                                            v_isShared_5619_ = v_isSharedCheck_5624_;
                                            state = 29;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5616_);
                                            lean_dec(v___x_5615_);
                                            v___x_5618_ = lean_box(0);
                                            v_isShared_5619_ = v_isSharedCheck_5624_;
                                            state = 29;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_5613_);
                                        return v___x_5615_;
                                    }
                                } else {
                                    lean_dec_ref_known(v_code_5426_, 1);
                                    lean_dec(v_fvarId_5603_);
                                    v_a_5625_ = lean_ctor_get(v___x_5612_, 0);
                                    v_isSharedCheck_5632_ = (!lean_is_exclusive(v___x_5612_)) as u8;
                                    if v_isSharedCheck_5632_ == 0 {
                                        v___x_5627_ = v___x_5612_;
                                        v_isShared_5628_ = v_isSharedCheck_5632_;
                                        state = 31;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5625_);
                                        lean_dec(v___x_5612_);
                                        v___x_5627_ = lean_box(0);
                                        v_isShared_5628_ = v_isSharedCheck_5632_;
                                        state = 31;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref_known(v_code_5426_, 1);
                                lean_dec(v_fvarId_5603_);
                                v_a_5633_ = lean_ctor_get(v___x_5608_, 0);
                                v_isSharedCheck_5640_ = (!lean_is_exclusive(v___x_5608_)) as u8;
                                if v_isSharedCheck_5640_ == 0 {
                                    v___x_5635_ = v___x_5608_;
                                    v_isShared_5636_ = v_isSharedCheck_5640_;
                                    state = 33;
                                    continue;
                                } else {
                                    lean_inc(v_a_5633_);
                                    lean_dec(v___x_5608_);
                                    v___x_5635_ = lean_box(0);
                                    v_isShared_5636_ = v_isSharedCheck_5640_;
                                    state = 33;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5605_);
                            lean_inc(v_fvarId_5603_);
                            v___x_5641_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_5603_, v_code_5426_, v_fvarId_5603_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                            lean_dec(v_fvarId_5603_);
                            return v___x_5641_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_5426_, 1);
                        lean_dec(v_fvarId_5603_);
                        v_a_5642_ = lean_ctor_get(v___x_5604_, 0);
                        v_isSharedCheck_5649_ = (!lean_is_exclusive(v___x_5604_)) as u8;
                        if v_isSharedCheck_5649_ == 0 {
                            v___x_5644_ = v___x_5604_;
                            v_isShared_5645_ = v_isSharedCheck_5649_;
                            state = 35;
                            continue;
                        } else {
                            lean_inc(v_a_5642_);
                            lean_dec(v___x_5604_);
                            v___x_5644_ = lean_box(0);
                            v_isShared_5645_ = v_isSharedCheck_5649_;
                            state = 35;
                            continue;
                        }
                    }
                }
                6 => {
                    v_type_5650_ = lean_ctor_get(v_code_5426_, 0);
                    v_currDeclResultType_5651_ = lean_ctor_get(v_a_5427_, 1);
                    v___x_5652_ = lean_ptr_addr(v_type_5650_);
                    v___x_5653_ = lean_ptr_addr(v_currDeclResultType_5651_);
                    v___x_5654_ = lean_usize_dec_eq(v___x_5652_, v___x_5653_);
                    if v___x_5654_ == 0 {
                        v_isSharedCheck_5662_ = (!lean_is_exclusive(v_code_5426_)) as u8;
                        if v_isSharedCheck_5662_ == 0 {
                            v_unused_5663_ = lean_ctor_get(v_code_5426_, 0);
                            lean_dec(v_unused_5663_);
                            v___x_5656_ = v_code_5426_;
                            v_isShared_5657_ = v_isSharedCheck_5662_;
                            state = 37;
                            continue;
                        } else {
                            lean_dec(v_code_5426_);
                            v___x_5656_ = lean_box(0);
                            v_isShared_5657_ = v_isSharedCheck_5662_;
                            state = 37;
                            continue;
                        }
                    } else {
                        v___x_5664_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5664_, 0, v_code_5426_);
                        return v___x_5664_;
                    }
                }
                8 => {
                    v_fvarId_5665_ = lean_ctor_get(v_code_5426_, 0);
                    lean_inc(v_fvarId_5665_);
                    v_i_5666_ = lean_ctor_get(v_code_5426_, 1);
                    lean_inc(v_i_5666_);
                    v_y_5667_ = lean_ctor_get(v_code_5426_, 2);
                    lean_inc(v_y_5667_);
                    v_k_5668_ = lean_ctor_get(v_code_5426_, 3);
                    lean_inc_ref_n(v_k_5668_, 2);
                    v___x_5669_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_5668_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                    if lean_obj_tag(v___x_5669_) == 0 {
                        v_a_5670_ = lean_ctor_get(v___x_5669_, 0);
                        lean_inc(v_a_5670_);
                        lean_dec_ref_known(v___x_5669_, 1);
                        lean_inc(v_y_5667_);
                        v___x_5671_ = l_Lean_Compiler_LCNF_getType(
                            v_y_5667_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_,
                        );
                        if lean_obj_tag(v___x_5671_) == 0 {
                            v_a_5672_ = lean_ctor_get(v___x_5671_, 0);
                            lean_inc(v_a_5672_);
                            lean_dec_ref_known(v___x_5671_, 1);
                            v___x_5673_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
                            v___x_5674_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_5672_, v___x_5673_);
                            if v___x_5674_ == 0 {
                                lean_inc(v_y_5667_);
                                v___x_5675_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_5667_, v_a_5672_, v___x_5673_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                if lean_obj_tag(v___x_5675_) == 0 {
                                    v_a_5676_ = lean_ctor_get(v___x_5675_, 0);
                                    lean_inc(v_a_5676_);
                                    lean_dec_ref_known(v___x_5675_, 1);
                                    v___x_5677_ = 1;
                                    v___x_5678_ = lean_box(0);
                                    v___x_5679_ = l_Lean_Compiler_LCNF_mkLetDecl(
                                        v___x_5677_,
                                        v___x_5678_,
                                        v___x_5673_,
                                        v_a_5676_,
                                        v_a_5429_,
                                        v_a_5430_,
                                        v_a_5431_,
                                        v_a_5432_,
                                    );
                                    if lean_obj_tag(v___x_5679_) == 0 {
                                        v_a_5680_ = lean_ctor_get(v___x_5679_, 0);
                                        lean_inc(v_a_5680_);
                                        lean_dec_ref_known(v___x_5679_, 1);
                                        v_fvarId_5681_ = lean_ctor_get(v_a_5680_, 0);
                                        lean_inc(v_fvarId_5681_);
                                        v___x_5682_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_5665_, v_i_5666_, v_a_5670_, v_y_5667_, v_k_5668_, v_code_5426_, v_fvarId_5681_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                        lean_dec_ref(v_k_5668_);
                                        lean_dec(v_y_5667_);
                                        if lean_obj_tag(v___x_5682_) == 0 {
                                            v_a_5683_ = lean_ctor_get(v___x_5682_, 0);
                                            v_isSharedCheck_5691_ =
                                                (!lean_is_exclusive(v___x_5682_)) as u8;
                                            if v_isSharedCheck_5691_ == 0 {
                                                v___x_5685_ = v___x_5682_;
                                                v_isShared_5686_ = v_isSharedCheck_5691_;
                                                state = 39;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5683_);
                                                lean_dec(v___x_5682_);
                                                v___x_5685_ = lean_box(0);
                                                v_isShared_5686_ = v_isSharedCheck_5691_;
                                                state = 39;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_5680_);
                                            return v___x_5682_;
                                        }
                                    } else {
                                        lean_dec(v_a_5670_);
                                        lean_dec_ref(v_k_5668_);
                                        lean_dec(v_y_5667_);
                                        lean_dec(v_i_5666_);
                                        lean_dec(v_fvarId_5665_);
                                        lean_dec_ref_known(v_code_5426_, 4);
                                        v_a_5692_ = lean_ctor_get(v___x_5679_, 0);
                                        v_isSharedCheck_5699_ =
                                            (!lean_is_exclusive(v___x_5679_)) as u8;
                                        if v_isSharedCheck_5699_ == 0 {
                                            v___x_5694_ = v___x_5679_;
                                            v_isShared_5695_ = v_isSharedCheck_5699_;
                                            state = 41;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5692_);
                                            lean_dec(v___x_5679_);
                                            v___x_5694_ = lean_box(0);
                                            v_isShared_5695_ = v_isSharedCheck_5699_;
                                            state = 41;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5670_);
                                    lean_dec_ref(v_k_5668_);
                                    lean_dec(v_y_5667_);
                                    lean_dec(v_i_5666_);
                                    lean_dec(v_fvarId_5665_);
                                    lean_dec_ref_known(v_code_5426_, 4);
                                    v_a_5700_ = lean_ctor_get(v___x_5675_, 0);
                                    v_isSharedCheck_5707_ = (!lean_is_exclusive(v___x_5675_)) as u8;
                                    if v_isSharedCheck_5707_ == 0 {
                                        v___x_5702_ = v___x_5675_;
                                        v_isShared_5703_ = v_isSharedCheck_5707_;
                                        state = 43;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5700_);
                                        lean_dec(v___x_5675_);
                                        v___x_5702_ = lean_box(0);
                                        v_isShared_5703_ = v_isSharedCheck_5707_;
                                        state = 43;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5672_);
                                lean_inc(v_y_5667_);
                                v___x_5708_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_5665_, v_i_5666_, v_a_5670_, v_y_5667_, v_k_5668_, v_code_5426_, v_y_5667_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                lean_dec_ref(v_k_5668_);
                                lean_dec(v_y_5667_);
                                return v___x_5708_;
                            }
                        } else {
                            lean_dec(v_a_5670_);
                            lean_dec_ref(v_k_5668_);
                            lean_dec(v_y_5667_);
                            lean_dec(v_i_5666_);
                            lean_dec(v_fvarId_5665_);
                            lean_dec_ref_known(v_code_5426_, 4);
                            v_a_5709_ = lean_ctor_get(v___x_5671_, 0);
                            v_isSharedCheck_5716_ = (!lean_is_exclusive(v___x_5671_)) as u8;
                            if v_isSharedCheck_5716_ == 0 {
                                v___x_5711_ = v___x_5671_;
                                v_isShared_5712_ = v_isSharedCheck_5716_;
                                state = 45;
                                continue;
                            } else {
                                lean_inc(v_a_5709_);
                                lean_dec(v___x_5671_);
                                v___x_5711_ = lean_box(0);
                                v_isShared_5712_ = v_isSharedCheck_5716_;
                                state = 45;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_k_5668_);
                        lean_dec(v_y_5667_);
                        lean_dec(v_i_5666_);
                        lean_dec(v_fvarId_5665_);
                        lean_dec_ref_known(v_code_5426_, 4);
                        return v___x_5669_;
                    }
                }
                9 => {
                    v_fvarId_5717_ = lean_ctor_get(v_code_5426_, 0);
                    lean_inc(v_fvarId_5717_);
                    v_i_5718_ = lean_ctor_get(v_code_5426_, 1);
                    lean_inc(v_i_5718_);
                    v_offset_5719_ = lean_ctor_get(v_code_5426_, 2);
                    lean_inc(v_offset_5719_);
                    v_y_5720_ = lean_ctor_get(v_code_5426_, 3);
                    lean_inc(v_y_5720_);
                    v_ty_5721_ = lean_ctor_get(v_code_5426_, 4);
                    lean_inc_ref(v_ty_5721_);
                    v_k_5722_ = lean_ctor_get(v_code_5426_, 5);
                    lean_inc_ref_n(v_k_5722_, 2);
                    v___x_5723_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_5722_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                    if lean_obj_tag(v___x_5723_) == 0 {
                        v_a_5724_ = lean_ctor_get(v___x_5723_, 0);
                        lean_inc(v_a_5724_);
                        lean_dec_ref_known(v___x_5723_, 1);
                        lean_inc(v_y_5720_);
                        v___x_5725_ = l_Lean_Compiler_LCNF_getType(
                            v_y_5720_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_,
                        );
                        if lean_obj_tag(v___x_5725_) == 0 {
                            v_a_5726_ = lean_ctor_get(v___x_5725_, 0);
                            lean_inc(v_a_5726_);
                            lean_dec_ref_known(v___x_5725_, 1);
                            v___x_5727_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_5726_, v_ty_5721_);
                            if v___x_5727_ == 0 {
                                lean_inc_ref(v_ty_5721_);
                                lean_inc(v_y_5720_);
                                v___x_5728_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_5720_, v_a_5726_, v_ty_5721_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                if lean_obj_tag(v___x_5728_) == 0 {
                                    v_a_5729_ = lean_ctor_get(v___x_5728_, 0);
                                    lean_inc(v_a_5729_);
                                    lean_dec_ref_known(v___x_5728_, 1);
                                    v___x_5730_ = 1;
                                    v___x_5731_ = lean_box(0);
                                    lean_inc_ref(v_ty_5721_);
                                    v___x_5732_ = l_Lean_Compiler_LCNF_mkLetDecl(
                                        v___x_5730_,
                                        v___x_5731_,
                                        v_ty_5721_,
                                        v_a_5729_,
                                        v_a_5429_,
                                        v_a_5430_,
                                        v_a_5431_,
                                        v_a_5432_,
                                    );
                                    if lean_obj_tag(v___x_5732_) == 0 {
                                        v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
                                        lean_inc(v_a_5733_);
                                        lean_dec_ref_known(v___x_5732_, 1);
                                        v_fvarId_5734_ = lean_ctor_get(v_a_5733_, 0);
                                        lean_inc(v_fvarId_5734_);
                                        v___x_5735_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_5717_, v_i_5718_, v_offset_5719_, v_ty_5721_, v_a_5724_, v_y_5720_, v_k_5722_, v_code_5426_, v_fvarId_5734_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                        lean_dec_ref(v_k_5722_);
                                        lean_dec(v_y_5720_);
                                        if lean_obj_tag(v___x_5735_) == 0 {
                                            v_a_5736_ = lean_ctor_get(v___x_5735_, 0);
                                            v_isSharedCheck_5744_ =
                                                (!lean_is_exclusive(v___x_5735_)) as u8;
                                            if v_isSharedCheck_5744_ == 0 {
                                                v___x_5738_ = v___x_5735_;
                                                v_isShared_5739_ = v_isSharedCheck_5744_;
                                                state = 47;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5736_);
                                                lean_dec(v___x_5735_);
                                                v___x_5738_ = lean_box(0);
                                                v_isShared_5739_ = v_isSharedCheck_5744_;
                                                state = 47;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_5733_);
                                            return v___x_5735_;
                                        }
                                    } else {
                                        lean_dec(v_a_5724_);
                                        lean_dec_ref(v_k_5722_);
                                        lean_dec_ref(v_ty_5721_);
                                        lean_dec(v_y_5720_);
                                        lean_dec(v_offset_5719_);
                                        lean_dec(v_i_5718_);
                                        lean_dec(v_fvarId_5717_);
                                        lean_dec_ref_known(v_code_5426_, 6);
                                        v_a_5745_ = lean_ctor_get(v___x_5732_, 0);
                                        v_isSharedCheck_5752_ =
                                            (!lean_is_exclusive(v___x_5732_)) as u8;
                                        if v_isSharedCheck_5752_ == 0 {
                                            v___x_5747_ = v___x_5732_;
                                            v_isShared_5748_ = v_isSharedCheck_5752_;
                                            state = 49;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5745_);
                                            lean_dec(v___x_5732_);
                                            v___x_5747_ = lean_box(0);
                                            v_isShared_5748_ = v_isSharedCheck_5752_;
                                            state = 49;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5724_);
                                    lean_dec_ref(v_k_5722_);
                                    lean_dec_ref(v_ty_5721_);
                                    lean_dec(v_y_5720_);
                                    lean_dec(v_offset_5719_);
                                    lean_dec(v_i_5718_);
                                    lean_dec(v_fvarId_5717_);
                                    lean_dec_ref_known(v_code_5426_, 6);
                                    v_a_5753_ = lean_ctor_get(v___x_5728_, 0);
                                    v_isSharedCheck_5760_ = (!lean_is_exclusive(v___x_5728_)) as u8;
                                    if v_isSharedCheck_5760_ == 0 {
                                        v___x_5755_ = v___x_5728_;
                                        v_isShared_5756_ = v_isSharedCheck_5760_;
                                        state = 51;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5753_);
                                        lean_dec(v___x_5728_);
                                        v___x_5755_ = lean_box(0);
                                        v_isShared_5756_ = v_isSharedCheck_5760_;
                                        state = 51;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5726_);
                                lean_inc(v_y_5720_);
                                v___x_5761_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_5717_, v_i_5718_, v_offset_5719_, v_ty_5721_, v_a_5724_, v_y_5720_, v_k_5722_, v_code_5426_, v_y_5720_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                                lean_dec_ref(v_k_5722_);
                                lean_dec(v_y_5720_);
                                return v___x_5761_;
                            }
                        } else {
                            lean_dec(v_a_5724_);
                            lean_dec_ref(v_k_5722_);
                            lean_dec_ref(v_ty_5721_);
                            lean_dec(v_y_5720_);
                            lean_dec(v_offset_5719_);
                            lean_dec(v_i_5718_);
                            lean_dec(v_fvarId_5717_);
                            lean_dec_ref_known(v_code_5426_, 6);
                            v_a_5762_ = lean_ctor_get(v___x_5725_, 0);
                            v_isSharedCheck_5769_ = (!lean_is_exclusive(v___x_5725_)) as u8;
                            if v_isSharedCheck_5769_ == 0 {
                                v___x_5764_ = v___x_5725_;
                                v_isShared_5765_ = v_isSharedCheck_5769_;
                                state = 53;
                                continue;
                            } else {
                                lean_inc(v_a_5762_);
                                lean_dec(v___x_5725_);
                                v___x_5764_ = lean_box(0);
                                v_isShared_5765_ = v_isSharedCheck_5769_;
                                state = 53;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_k_5722_);
                        lean_dec_ref(v_ty_5721_);
                        lean_dec(v_y_5720_);
                        lean_dec(v_offset_5719_);
                        lean_dec(v_i_5718_);
                        lean_dec(v_fvarId_5717_);
                        lean_dec_ref_known(v_code_5426_, 6);
                        return v___x_5723_;
                    }
                }
                _ => {
                    lean_dec_ref(v_code_5426_);
                    v___x_5770_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2);
                    v___x_5771_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_5770_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
                    return v___x_5771_;
                }
            },
            1 => {
                v___x_5469_ = lean_ptr_addr(v_k_5438_);
                v___x_5470_ = lean_ptr_addr(v_a_5448_);
                v___x_5471_ = lean_usize_dec_eq(v___x_5469_, v___x_5470_);
                if v___x_5471_ == 0 {
                    v___y_5453_ = v___x_5471_;
                    state = 2;
                    continue;
                } else {
                    v___x_5472_ = lean_ptr_addr(v_decl_5437_);
                    v___x_5473_ = lean_ptr_addr(v_a_5446_);
                    v___x_5474_ = lean_usize_dec_eq(v___x_5472_, v___x_5473_);
                    v___y_5453_ = v___x_5474_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_5453_ == 0 {
                    v_isSharedCheck_5463_ = (!lean_is_exclusive(v_code_5426_)) as u8;
                    if v_isSharedCheck_5463_ == 0 {
                        v_unused_5464_ = lean_ctor_get(v_code_5426_, 1);
                        lean_dec(v_unused_5464_);
                        v_unused_5465_ = lean_ctor_get(v_code_5426_, 0);
                        lean_dec(v_unused_5465_);
                        v___x_5455_ = v_code_5426_;
                        v_isShared_5456_ = v_isSharedCheck_5463_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_code_5426_);
                        v___x_5455_ = lean_box(0);
                        v_isShared_5456_ = v_isSharedCheck_5463_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5448_);
                    lean_dec(v_a_5446_);
                    if v_isShared_5451_ == 0 {
                        lean_ctor_set(v___x_5450_, 0, v_code_5426_);
                        v___x_5467_ = v___x_5450_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5468_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_code_5426_);
                        v___x_5467_ = v_reuseFailAlloc_5468_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5456_ == 0 {
                    lean_ctor_set(v___x_5455_, 1, v_a_5448_);
                    lean_ctor_set(v___x_5455_, 0, v_a_5446_);
                    v___x_5458_ = v___x_5455_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5462_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5446_);
                    lean_ctor_set(v_reuseFailAlloc_5462_, 1, v_a_5448_);
                    v___x_5458_ = v_reuseFailAlloc_5462_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5451_ == 0 {
                    lean_ctor_set(v___x_5450_, 0, v___x_5458_);
                    v___x_5460_ = v___x_5450_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5458_);
                    v___x_5460_ = v_reuseFailAlloc_5461_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5460_;
            }
            6 => {
                return v___x_5467_;
            }
            7 => {
                if v_isShared_5479_ == 0 {
                    v___x_5481_ = v___x_5478_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5482_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5476_);
                    v___x_5481_ = v_reuseFailAlloc_5482_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5481_;
            }
            9 => {
                v_fst_5498_ = lean_ctor_get(v_a_5494_, 0);
                lean_inc(v_fst_5498_);
                v_snd_5499_ = lean_ctor_get(v_a_5494_, 1);
                lean_inc(v_snd_5499_);
                lean_dec(v_a_5494_);
                v___x_5517_ = l_Lean_instBEqFVarId_beq(v_fvarId_5484_, v_fvarId_5484_);
                if v___x_5517_ == 0 {
                    v___y_5507_ = v___x_5517_;
                    state = 12;
                    continue;
                } else {
                    v___x_5518_ = lean_ptr_addr(v_args_5485_);
                    v___x_5519_ = lean_ptr_addr(v_fst_5498_);
                    v___x_5520_ = lean_usize_dec_eq(v___x_5518_, v___x_5519_);
                    v___y_5507_ = v___x_5520_;
                    state = 12;
                    continue;
                }
            }
            10 => {
                v___x_5502_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5486_, v_snd_5499_, v___y_5501_);
                lean_dec(v_snd_5499_);
                if v_isShared_5497_ == 0 {
                    lean_ctor_set(v___x_5496_, 0, v___x_5502_);
                    v___x_5504_ = v___x_5496_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5502_);
                    v___x_5504_ = v_reuseFailAlloc_5505_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5504_;
            }
            12 => {
                if v___y_5507_ == 0 {
                    lean_inc(v_fvarId_5484_);
                    v_isSharedCheck_5514_ = (!lean_is_exclusive(v_code_5426_)) as u8;
                    if v_isSharedCheck_5514_ == 0 {
                        v_unused_5515_ = lean_ctor_get(v_code_5426_, 1);
                        lean_dec(v_unused_5515_);
                        v_unused_5516_ = lean_ctor_get(v_code_5426_, 0);
                        lean_dec(v_unused_5516_);
                        v___x_5509_ = v_code_5426_;
                        v_isShared_5510_ = v_isSharedCheck_5514_;
                        state = 13;
                        continue;
                    } else {
                        lean_dec(v_code_5426_);
                        v___x_5509_ = lean_box(0);
                        v_isShared_5510_ = v_isSharedCheck_5514_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_5498_);
                    v___y_5501_ = v_code_5426_;
                    state = 10;
                    continue;
                }
            }
            13 => {
                if v_isShared_5510_ == 0 {
                    lean_ctor_set(v___x_5509_, 1, v_fst_5498_);
                    v___x_5512_ = v___x_5509_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5513_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_fvarId_5484_);
                    lean_ctor_set(v_reuseFailAlloc_5513_, 1, v_fst_5498_);
                    v___x_5512_ = v_reuseFailAlloc_5513_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_5501_ = v___x_5512_;
                state = 10;
                continue;
            }
            15 => {
                if v_isShared_5525_ == 0 {
                    v___x_5527_ = v___x_5524_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_a_5522_);
                    v___x_5527_ = v_reuseFailAlloc_5528_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5527_;
            }
            17 => {
                if v_isShared_5535_ == 0 {
                    v___x_5537_ = v___x_5534_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
                    v___x_5537_ = v_reuseFailAlloc_5538_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5537_;
            }
            19 => {
                v___x_5565_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5565_, 0, v_a_5558_);
                lean_ctor_set(v___x_5565_, 1, v_a_5561_);
                if v_isShared_5564_ == 0 {
                    lean_ctor_set(v___x_5563_, 0, v___x_5565_);
                    v___x_5567_ = v___x_5563_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5565_);
                    v___x_5567_ = v_reuseFailAlloc_5568_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5567_;
            }
            21 => {
                if v_isShared_5573_ == 0 {
                    v___x_5575_ = v___x_5572_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5576_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_a_5570_);
                    v___x_5575_ = v_reuseFailAlloc_5576_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5575_;
            }
            23 => {
                if v_isShared_5581_ == 0 {
                    v___x_5583_ = v___x_5580_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5584_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_a_5578_);
                    v___x_5583_ = v_reuseFailAlloc_5584_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5583_;
            }
            25 => {
                if v_isShared_5590_ == 0 {
                    v___x_5592_ = v___x_5589_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5587_);
                    v___x_5592_ = v_reuseFailAlloc_5593_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5592_;
            }
            27 => {
                if v_isShared_5598_ == 0 {
                    v___x_5600_ = v___x_5597_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5595_);
                    v___x_5600_ = v_reuseFailAlloc_5601_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5600_;
            }
            29 => {
                v___x_5620_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5620_, 0, v_a_5613_);
                lean_ctor_set(v___x_5620_, 1, v_a_5616_);
                if v_isShared_5619_ == 0 {
                    lean_ctor_set(v___x_5618_, 0, v___x_5620_);
                    v___x_5622_ = v___x_5618_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5620_);
                    v___x_5622_ = v_reuseFailAlloc_5623_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5622_;
            }
            31 => {
                if v_isShared_5628_ == 0 {
                    v___x_5630_ = v___x_5627_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5631_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_a_5625_);
                    v___x_5630_ = v_reuseFailAlloc_5631_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5630_;
            }
            33 => {
                if v_isShared_5636_ == 0 {
                    v___x_5638_ = v___x_5635_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5639_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_a_5633_);
                    v___x_5638_ = v_reuseFailAlloc_5639_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5638_;
            }
            35 => {
                if v_isShared_5645_ == 0 {
                    v___x_5647_ = v___x_5644_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5648_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_a_5642_);
                    v___x_5647_ = v_reuseFailAlloc_5648_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5647_;
            }
            37 => {
                lean_inc_ref(v_currDeclResultType_5651_);
                if v_isShared_5657_ == 0 {
                    lean_ctor_set(v___x_5656_, 0, v_currDeclResultType_5651_);
                    v___x_5659_ = v___x_5656_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5661_ = lean_alloc_ctor(6, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_currDeclResultType_5651_);
                    v___x_5659_ = v_reuseFailAlloc_5661_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_5660_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5660_, 0, v___x_5659_);
                return v___x_5660_;
            }
            39 => {
                v___x_5687_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5687_, 0, v_a_5680_);
                lean_ctor_set(v___x_5687_, 1, v_a_5683_);
                if v_isShared_5686_ == 0 {
                    lean_ctor_set(v___x_5685_, 0, v___x_5687_);
                    v___x_5689_ = v___x_5685_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5690_, 0, v___x_5687_);
                    v___x_5689_ = v_reuseFailAlloc_5690_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5689_;
            }
            41 => {
                if v_isShared_5695_ == 0 {
                    v___x_5697_ = v___x_5694_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_5698_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_a_5692_);
                    v___x_5697_ = v_reuseFailAlloc_5698_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_5697_;
            }
            43 => {
                if v_isShared_5703_ == 0 {
                    v___x_5705_ = v___x_5702_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5706_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5706_, 0, v_a_5700_);
                    v___x_5705_ = v_reuseFailAlloc_5706_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_5705_;
            }
            45 => {
                if v_isShared_5712_ == 0 {
                    v___x_5714_ = v___x_5711_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
                    v___x_5714_ = v_reuseFailAlloc_5715_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_5714_;
            }
            47 => {
                v___x_5740_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5740_, 0, v_a_5733_);
                lean_ctor_set(v___x_5740_, 1, v_a_5736_);
                if v_isShared_5739_ == 0 {
                    lean_ctor_set(v___x_5738_, 0, v___x_5740_);
                    v___x_5742_ = v___x_5738_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5743_, 0, v___x_5740_);
                    v___x_5742_ = v_reuseFailAlloc_5743_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_5742_;
            }
            49 => {
                if v_isShared_5748_ == 0 {
                    v___x_5750_ = v___x_5747_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
                    v___x_5750_ = v_reuseFailAlloc_5751_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_5750_;
            }
            51 => {
                if v_isShared_5756_ == 0 {
                    v___x_5758_ = v___x_5755_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_a_5753_);
                    v___x_5758_ = v_reuseFailAlloc_5759_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5758_;
            }
            53 => {
                if v_isShared_5765_ == 0 {
                    v___x_5767_ = v___x_5764_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_5768_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
                    v___x_5767_ = v_reuseFailAlloc_5768_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_5767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed(
    mut v_code_5772_: *mut LeanObject,
    mut v_a_5773_: *mut LeanObject,
    mut v_a_5774_: *mut LeanObject,
    mut v_a_5775_: *mut LeanObject,
    mut v_a_5776_: *mut LeanObject,
    mut v_a_5777_: *mut LeanObject,
    mut v_a_5778_: *mut LeanObject,
    mut v_a_5779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5780_: *mut LeanObject = core::ptr::null_mut();
    v_res_5780_ =
        l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(
            v_code_5772_,
            v_a_5773_,
            v_a_5774_,
            v_a_5775_,
            v_a_5776_,
            v_a_5777_,
            v_a_5778_,
        );
    lean_dec(v_a_5778_);
    lean_dec_ref(v_a_5777_);
    lean_dec(v_a_5776_);
    lean_dec_ref(v_a_5775_);
    lean_dec(v_a_5774_);
    lean_dec_ref(v_a_5773_);
    return v_res_5780_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(
    mut v_i_5781_: *mut LeanObject,
    mut v_as_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
    mut v___y_5784_: *mut LeanObject,
    mut v___y_5785_: *mut LeanObject,
    mut v___y_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
    mut v___y_5788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: u8 = 0;
    let mut v___x_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: usize = 0;
    let mut v___x_5798_: usize = 0;
    let mut v___x_5799_: u8 = 0;
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5810_: u8 = 0;
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5790_ = lean_array_get_size(v_as_5782_);
                v___x_5791_ = lean_nat_dec_lt(v_i_5781_, v___x_5790_);
                if v___x_5791_ == 0 {
                    lean_dec(v_i_5781_);
                    v___x_5792_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5792_, 0, v_as_5782_);
                    return v___x_5792_;
                } else {
                    v___f_5793_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed as *mut core::ffi::c_void, 8, 0);
                    v_a_5794_ = lean_array_fget_borrowed(v_as_5782_, v_i_5781_);
                    lean_inc(v_a_5794_);
                    v___x_5795_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_a_5794_, v___f_5793_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
                    if lean_obj_tag(v___x_5795_) == 0 {
                        v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
                        lean_inc(v_a_5796_);
                        lean_dec_ref_known(v___x_5795_, 1);
                        v___x_5797_ = lean_ptr_addr(v_a_5794_);
                        v___x_5798_ = lean_ptr_addr(v_a_5796_);
                        v___x_5799_ = lean_usize_dec_eq(v___x_5797_, v___x_5798_);
                        if v___x_5799_ == 0 {
                            v___x_5800_ = lean_unsigned_to_nat(1);
                            v___x_5801_ = lean_nat_add(v_i_5781_, v___x_5800_);
                            v___x_5802_ = lean_array_fset(v_as_5782_, v_i_5781_, v_a_5796_);
                            lean_dec(v_i_5781_);
                            v_i_5781_ = v___x_5801_;
                            v_as_5782_ = v___x_5802_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_5796_);
                            v___x_5804_ = lean_unsigned_to_nat(1);
                            v___x_5805_ = lean_nat_add(v_i_5781_, v___x_5804_);
                            lean_dec(v_i_5781_);
                            v_i_5781_ = v___x_5805_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_5782_);
                        lean_dec(v_i_5781_);
                        v_a_5807_ = lean_ctor_get(v___x_5795_, 0);
                        v_isSharedCheck_5814_ = (!lean_is_exclusive(v___x_5795_)) as u8;
                        if v_isSharedCheck_5814_ == 0 {
                            v___x_5809_ = v___x_5795_;
                            v_isShared_5810_ = v_isSharedCheck_5814_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5807_);
                            lean_dec(v___x_5795_);
                            v___x_5809_ = lean_box(0);
                            v_isShared_5810_ = v_isSharedCheck_5814_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5810_ == 0 {
                    v___x_5812_ = v___x_5809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5813_, 0, v_a_5807_);
                    v___x_5812_ = v_reuseFailAlloc_5813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3___boxed(
    mut v_i_5815_: *mut LeanObject,
    mut v_as_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
    mut v___y_5819_: *mut LeanObject,
    mut v___y_5820_: *mut LeanObject,
    mut v___y_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
    mut v___y_5823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5824_: *mut LeanObject = core::ptr::null_mut();
    v_res_5824_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v_i_5815_, v_as_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_);
    lean_dec(v___y_5822_);
    lean_dec_ref(v___y_5821_);
    lean_dec(v___y_5820_);
    lean_dec_ref(v___y_5819_);
    lean_dec(v___y_5818_);
    lean_dec_ref(v___y_5817_);
    return v_res_5824_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___boxed(
    mut v_code_5825_: *mut LeanObject,
    mut v_decl_5826_: *mut LeanObject,
    mut v_k_5827_: *mut LeanObject,
    mut v_a_5828_: *mut LeanObject,
    mut v_a_5829_: *mut LeanObject,
    mut v_a_5830_: *mut LeanObject,
    mut v_a_5831_: *mut LeanObject,
    mut v_a_5832_: *mut LeanObject,
    mut v_a_5833_: *mut LeanObject,
    mut v_a_5834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5835_: *mut LeanObject = core::ptr::null_mut();
    v_res_5835_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_5825_, v_decl_5826_, v_k_5827_, v_a_5828_, v_a_5829_, v_a_5830_, v_a_5831_, v_a_5832_, v_a_5833_);
    lean_dec(v_a_5833_);
    lean_dec_ref(v_a_5832_);
    lean_dec(v_a_5831_);
    lean_dec_ref(v_a_5830_);
    lean_dec(v_a_5829_);
    lean_dec_ref(v_a_5828_);
    return v_res_5835_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(
    mut v_pu_5836_: u8,
    mut v_alt_5837_: *mut LeanObject,
    mut v_f_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    v___x_5846_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_5837_, v_f_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
    return v___x_5846_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___boxed(
    mut v_pu_5847_: *mut LeanObject,
    mut v_alt_5848_: *mut LeanObject,
    mut v_f_5849_: *mut LeanObject,
    mut v___y_5850_: *mut LeanObject,
    mut v___y_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
    mut v___y_5854_: *mut LeanObject,
    mut v___y_5855_: *mut LeanObject,
    mut v___y_5856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5857_: u8 = 0;
    let mut v_res_5858_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5857_ = (lean_unbox(v_pu_5847_) as u8);
    v_res_5858_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(v_pu_boxed_5857_, v_alt_5848_, v_f_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_);
    lean_dec(v___y_5855_);
    lean_dec_ref(v___y_5854_);
    lean_dec(v___y_5853_);
    lean_dec_ref(v___y_5852_);
    lean_dec(v___y_5851_);
    lean_dec_ref(v___y_5850_);
    return v_res_5858_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(
    mut v_as_5862_: *mut LeanObject,
    mut v_i_5863_: usize,
    mut v_stop_5864_: usize,
    mut v_b_5865_: *mut LeanObject,
    mut v___y_5866_: *mut LeanObject,
    mut v___y_5867_: *mut LeanObject,
    mut v___y_5868_: *mut LeanObject,
    mut v___y_5869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: usize = 0;
    let mut v___x_5874_: usize = 0;
    let mut v___x_5876_: u8 = 0;
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_5880_: u8 = 0;
    let mut v_inlineAttr_x3f_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5884_: u8 = 0;
    let mut v_code_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5888_: u8 = 0;
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: u8 = 0;
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDecls_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5910_: u8 = 0;
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5914_: u8 = 0;
    let mut v_reuseFailAlloc_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5920_: u8 = 0;
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5924_: u8 = 0;
    let mut v_isSharedCheck_5925_: u8 = 0;
    let mut v_isSharedCheck_5926_: u8 = 0;
    let mut v_unused_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5876_ = lean_usize_dec_eq(v_i_5863_, v_stop_5864_);
                if v___x_5876_ == 0 {
                    v___x_5877_ = lean_array_uget(v_as_5862_, v_i_5863_);
                    v_value_5878_ = lean_ctor_get(v___x_5877_, 1);
                    lean_inc_ref(v_value_5878_);
                    if lean_obj_tag(v_value_5878_) == 0 {
                        v_toSignature_5879_ = lean_ctor_get(v___x_5877_, 0);
                        v_recursive_5880_ = lean_ctor_get_uint8(
                            v___x_5877_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_inlineAttr_x3f_5881_ = lean_ctor_get(v___x_5877_, 2);
                        v_isSharedCheck_5926_ = (!lean_is_exclusive(v___x_5877_)) as u8;
                        if v_isSharedCheck_5926_ == 0 {
                            v_unused_5927_ = lean_ctor_get(v___x_5877_, 1);
                            lean_dec(v_unused_5927_);
                            v___x_5883_ = v___x_5877_;
                            v_isShared_5884_ = v_isSharedCheck_5926_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_inlineAttr_x3f_5881_);
                            lean_inc(v_toSignature_5879_);
                            lean_dec(v___x_5877_);
                            v___x_5883_ = lean_box(0);
                            v_isShared_5884_ = v_isSharedCheck_5926_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_value_5878_, 1);
                        v___x_5928_ = lean_array_push(v_b_5865_, v___x_5877_);
                        v_a_5872_ = v___x_5928_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5929_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5929_, 0, v_b_5865_);
                    return v___x_5929_;
                }
            }
            1 => {
                v___x_5873_ = 1usize;
                v___x_5874_ = lean_usize_add(v_i_5863_, v___x_5873_);
                v_i_5863_ = v___x_5874_;
                v_b_5865_ = v_a_5872_;
                state = 0;
                continue;
            }
            2 => {
                v_code_5885_ = lean_ctor_get(v_value_5878_, 0);
                v_isSharedCheck_5925_ = (!lean_is_exclusive(v_value_5878_)) as u8;
                if v_isSharedCheck_5925_ == 0 {
                    v___x_5887_ = v_value_5878_;
                    v_isShared_5888_ = v_isSharedCheck_5925_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_code_5885_);
                    lean_dec(v_value_5878_);
                    v___x_5887_ = lean_box(0);
                    v_isShared_5888_ = v_isSharedCheck_5925_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0;
                v___x_5890_ = lean_st_mk_ref(v___x_5889_);
                v_name_5891_ = lean_ctor_get(v_toSignature_5879_, 0);
                v_type_5892_ = lean_ctor_get(v_toSignature_5879_, 2);
                lean_inc_ref(v_type_5892_);
                lean_inc(v_name_5891_);
                v_s_5893_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_s_5893_, 0, v_name_5891_);
                lean_ctor_set(v_s_5893_, 1, v_type_5892_);
                v___x_5894_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_5885_, v_s_5893_, v___x_5890_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_);
                lean_dec_ref_known(v_s_5893_, 2);
                if lean_obj_tag(v___x_5894_) == 0 {
                    v_a_5895_ = lean_ctor_get(v___x_5894_, 0);
                    lean_inc(v_a_5895_);
                    lean_dec_ref_known(v___x_5894_, 1);
                    v___x_5896_ = lean_st_ref_get(v___x_5890_);
                    lean_dec(v___x_5890_);
                    v___x_5897_ = 1;
                    if v_isShared_5888_ == 0 {
                        lean_ctor_set(v___x_5887_, 0, v_a_5895_);
                        v___x_5899_ = v___x_5887_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5916_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5916_, 0, v_a_5895_);
                        v___x_5899_ = v_reuseFailAlloc_5916_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5890_);
                    lean_del_object(v___x_5887_);
                    lean_del_object(v___x_5883_);
                    lean_dec(v_inlineAttr_x3f_5881_);
                    lean_dec_ref(v_toSignature_5879_);
                    lean_dec_ref(v_b_5865_);
                    v_a_5917_ = lean_ctor_get(v___x_5894_, 0);
                    v_isSharedCheck_5924_ = (!lean_is_exclusive(v___x_5894_)) as u8;
                    if v_isSharedCheck_5924_ == 0 {
                        v___x_5919_ = v___x_5894_;
                        v_isShared_5920_ = v_isSharedCheck_5924_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5917_);
                        lean_dec(v___x_5894_);
                        v___x_5919_ = lean_box(0);
                        v_isShared_5920_ = v_isSharedCheck_5924_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5884_ == 0 {
                    lean_ctor_set(v___x_5883_, 1, v___x_5899_);
                    v___x_5901_ = v___x_5883_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5915_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_toSignature_5879_);
                    lean_ctor_set(v_reuseFailAlloc_5915_, 1, v___x_5899_);
                    lean_ctor_set(v_reuseFailAlloc_5915_, 2, v_inlineAttr_x3f_5881_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5915_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_5880_,
                    );
                    v___x_5901_ = v_reuseFailAlloc_5915_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5902_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(
                    v___x_5897_,
                    v___x_5901_,
                    v___y_5866_,
                    v___y_5867_,
                    v___y_5868_,
                    v___y_5869_,
                );
                if lean_obj_tag(v___x_5902_) == 0 {
                    v_a_5903_ = lean_ctor_get(v___x_5902_, 0);
                    lean_inc(v_a_5903_);
                    lean_dec_ref_known(v___x_5902_, 1);
                    v_auxDecls_5904_ = lean_ctor_get(v___x_5896_, 0);
                    lean_inc_ref(v_auxDecls_5904_);
                    lean_dec(v___x_5896_);
                    v___x_5905_ = l_Array_append___redArg(v_b_5865_, v_auxDecls_5904_);
                    lean_dec_ref(v_auxDecls_5904_);
                    v___x_5906_ = lean_array_push(v___x_5905_, v_a_5903_);
                    v_a_5872_ = v___x_5906_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_5896_);
                    lean_dec_ref(v_b_5865_);
                    v_a_5907_ = lean_ctor_get(v___x_5902_, 0);
                    v_isSharedCheck_5914_ = (!lean_is_exclusive(v___x_5902_)) as u8;
                    if v_isSharedCheck_5914_ == 0 {
                        v___x_5909_ = v___x_5902_;
                        v_isShared_5910_ = v_isSharedCheck_5914_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5907_);
                        lean_dec(v___x_5902_);
                        v___x_5909_ = lean_box(0);
                        v_isShared_5910_ = v_isSharedCheck_5914_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5910_ == 0 {
                    v___x_5912_ = v___x_5909_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5913_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_a_5907_);
                    v___x_5912_ = v_reuseFailAlloc_5913_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5912_;
            }
            8 => {
                if v_isShared_5920_ == 0 {
                    v___x_5922_ = v___x_5919_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_a_5917_);
                    v___x_5922_ = v_reuseFailAlloc_5923_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___boxed(
    mut v_as_5930_: *mut LeanObject,
    mut v_i_5931_: *mut LeanObject,
    mut v_stop_5932_: *mut LeanObject,
    mut v_b_5933_: *mut LeanObject,
    mut v___y_5934_: *mut LeanObject,
    mut v___y_5935_: *mut LeanObject,
    mut v___y_5936_: *mut LeanObject,
    mut v___y_5937_: *mut LeanObject,
    mut v___y_5938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5939_: usize = 0;
    let mut v_stop_boxed_5940_: usize = 0;
    let mut v_res_5941_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5939_ = lean_unbox_usize(v_i_5931_);
    lean_dec(v_i_5931_);
    v_stop_boxed_5940_ = lean_unbox_usize(v_stop_5932_);
    lean_dec(v_stop_5932_);
    v_res_5941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_as_5930_, v_i_boxed_5939_, v_stop_boxed_5940_, v_b_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_);
    lean_dec(v___y_5937_);
    lean_dec_ref(v___y_5936_);
    lean_dec(v___y_5935_);
    lean_dec_ref(v___y_5934_);
    lean_dec_ref(v_as_5930_);
    return v_res_5941_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(
    mut v_decls_5942_: *mut LeanObject,
    mut v_a_5943_: *mut LeanObject,
    mut v_a_5944_: *mut LeanObject,
    mut v_a_5945_: *mut LeanObject,
    mut v_a_5946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: u8 = 0;
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: u8 = 0;
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: usize = 0;
    let mut v___x_5960_: usize = 0;
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: usize = 0;
    let mut v___x_5963_: usize = 0;
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5952_ = lean_unsigned_to_nat(0);
                v___x_5953_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0;
                v___x_5954_ = lean_array_get_size(v_decls_5942_);
                v___x_5955_ = lean_nat_dec_lt(v___x_5952_, v___x_5954_);
                if v___x_5955_ == 0 {
                    v___x_5956_ = l_Lean_Compiler_LCNF_addBoxedVersions(
                        v___x_5953_,
                        v_a_5943_,
                        v_a_5944_,
                        v_a_5945_,
                        v_a_5946_,
                    );
                    return v___x_5956_;
                } else {
                    v___x_5957_ = lean_nat_dec_le(v___x_5954_, v___x_5954_);
                    if v___x_5957_ == 0 {
                        if v___x_5955_ == 0 {
                            v___x_5958_ = l_Lean_Compiler_LCNF_addBoxedVersions(
                                v___x_5953_,
                                v_a_5943_,
                                v_a_5944_,
                                v_a_5945_,
                                v_a_5946_,
                            );
                            return v___x_5958_;
                        } else {
                            v___x_5959_ = 0usize;
                            v___x_5960_ = lean_usize_of_nat(v___x_5954_);
                            v___x_5961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_5942_, v___x_5959_, v___x_5960_, v___x_5953_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
                            v___y_5949_ = v___x_5961_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_5962_ = 0usize;
                        v___x_5963_ = lean_usize_of_nat(v___x_5954_);
                        v___x_5964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_5942_, v___x_5962_, v___x_5963_, v___x_5953_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
                        v___y_5949_ = v___x_5964_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_5949_) == 0 {
                    v_a_5950_ = lean_ctor_get(v___y_5949_, 0);
                    lean_inc(v_a_5950_);
                    lean_dec_ref_known(v___y_5949_, 1);
                    v___x_5951_ = l_Lean_Compiler_LCNF_addBoxedVersions(
                        v_a_5950_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_,
                    );
                    return v___x_5951_;
                } else {
                    return v___y_5949_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed(
    mut v_decls_5965_: *mut LeanObject,
    mut v_a_5966_: *mut LeanObject,
    mut v_a_5967_: *mut LeanObject,
    mut v_a_5968_: *mut LeanObject,
    mut v_a_5969_: *mut LeanObject,
    mut v_a_5970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5971_: *mut LeanObject = core::ptr::null_mut();
    v_res_5971_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(
        v_decls_5965_,
        v_a_5966_,
        v_a_5967_,
        v_a_5968_,
        v_a_5969_,
    );
    lean_dec(v_a_5969_);
    lean_dec_ref(v_a_5968_);
    lean_dec(v_a_5967_);
    lean_dec_ref(v_a_5966_);
    lean_dec_ref(v_decls_5965_);
    return v_res_5971_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: u8 = 0;
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    v___x_6053_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_;
    v___x_6054_ = 1;
    v___x_6055_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_;
    v___x_6056_ = l_Lean_registerTraceClass(v___x_6053_, v___x_6054_, v___x_6055_);
    return v___x_6056_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2____boxed(
    mut v_a_6057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6058_: *mut LeanObject = core::ptr::null_mut();
    v_res_6058_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
    return v_res_6058_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Runtime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Runtime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
}
