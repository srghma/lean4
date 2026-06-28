// Lean compiler output
// Module: Lean.Compiler.LCNF.Internalize
// Imports: Lean.Compiler.LCNF.Bind
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg, l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg,
    l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_num___override,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadLift___lam__0___boxed, l_instInhabitedForall___redArg___lam__0___boxed,
    l_instInhabitedOfMonad___redArg, l_instMonadLiftT___lam__0___boxed,
    l_instMonadLiftTOfMonadLift___redArg___lam__0, l_instMonadStateOfMonadStateOf___redArg,
    l_instMonadStateOfOfMonadLift___redArg___lam__0,
    l_instMonadStateOfOfMonadLift___redArg___lam__1, l_modify,
};
use crate::r#gen::Init::System::IO::{
    l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, l_instMonadEIO,
    l_instMonadLiftBaseIOEIO___lam__0___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp,
    l_Lean_Compiler_LCNF_instDecidableEqPurity, l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default,
};
use crate::r#gen::Lean::Compiler::LCNF::Bind::{
    initialize_Lean_Compiler_LCNF_Bind, runtime_initialize_Lean_Compiler_LCNF_Bind,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go,
    l_Lean_Compiler_LCNF_CompilerM_run___redArg, l_Lean_Compiler_LCNF_findParam_x3f___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, l_Lean_Compiler_LCNF_mkReturnErased,
    l_Lean_Compiler_LCNF_normFVarImp___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::{
    l_Lean_Compiler_LCNF_LCtx_addFunDecl, l_Lean_Compiler_LCNF_LCtx_addLetDecl,
    l_Lean_Compiler_LCNF_LCtx_addParam,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_anyExpr, l_Lean_Compiler_LCNF_erasedExpr,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_liftIOCore___boxed,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_fvar___override,
    l_Lean_Expr_hasFVar, l_Lean_Expr_headBeta, l_Lean_Expr_lam___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_instBEqBinderInfo_beq,
    l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash, l_Lean_instInhabitedExpr,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_liftIOCore___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftBaseIOEIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1_value: crate::leanh::LeanStringObject<92> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 46, 105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 69, 120, 112, 114, 46, 103, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0_value:
    crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73,
        110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 46, 105, 110, 116, 101, 114, 110, 97, 108,
        105, 122, 101, 67, 111, 100, 101, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_cleanup___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_cleanup___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_cleanup___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_cleanup___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [95, 117, 110, 105, 113, 0],
};
static mut l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3978731030111751661 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(
    mut v_x_3065_: *mut crate::leanh::LeanObject,
    mut v_state_3066_: *mut crate::leanh::LeanObject,
    mut v_ctx_3067_: u8,
    mut v_a_3068_: *mut crate::leanh::LeanObject,
    mut v_a_3069_: *mut crate::leanh::LeanObject,
    mut v_a_3070_: *mut crate::leanh::LeanObject,
    mut v_a_3071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut v_a_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3093_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3073_ = lean_st_mk_ref(v_state_3066_);
                v___x_3074_ = crate::leanh::lean_box((v_ctx_3067_) as usize);
                crate::leanh::lean_inc(v_a_3071_);
                crate::leanh::lean_inc_ref(v_a_3070_);
                crate::leanh::lean_inc(v_a_3069_);
                crate::leanh::lean_inc_ref(v_a_3068_);
                crate::leanh::lean_inc(v___x_3073_);
                v___x_3075_ = crate::leanh::lean_apply_7(
                    v_x_3065_,
                    v___x_3074_,
                    v___x_3073_,
                    v_a_3068_,
                    v_a_3069_,
                    v_a_3070_,
                    v_a_3071_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3075_) == 0 {
                    v_a_3076_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                    v_isSharedCheck_3085_ = (!crate::leanh::lean_is_exclusive(v___x_3075_)) as u8;
                    if v_isSharedCheck_3085_ == 0 {
                        v___x_3078_ = v___x_3075_;
                        v_isShared_3079_ = v_isSharedCheck_3085_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3076_);
                        crate::leanh::lean_dec(v___x_3075_);
                        v___x_3078_ = crate::leanh::lean_box(0);
                        v_isShared_3079_ = v_isSharedCheck_3085_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3073_);
                    v_a_3086_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                    v_isSharedCheck_3093_ = (!crate::leanh::lean_is_exclusive(v___x_3075_)) as u8;
                    if v_isSharedCheck_3093_ == 0 {
                        v___x_3088_ = v___x_3075_;
                        v_isShared_3089_ = v_isSharedCheck_3093_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3086_);
                        crate::leanh::lean_dec(v___x_3075_);
                        v___x_3088_ = crate::leanh::lean_box(0);
                        v_isShared_3089_ = v_isSharedCheck_3093_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3080_ = lean_st_ref_get(v___x_3073_);
                crate::leanh::lean_dec(v___x_3073_);
                v___x_3081_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3081_, 0, v_a_3076_);
                crate::leanh::lean_ctor_set(v___x_3081_, 1, v___x_3080_);
                if v_isShared_3079_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3078_, 0, v___x_3081_);
                    v___x_3083_ = v___x_3078_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3081_);
                    v___x_3083_ = v_reuseFailAlloc_3084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3083_;
            }
            3 => {
                if v_isShared_3089_ == 0 {
                    v___x_3091_ = v___x_3088_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3092_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
                    v___x_3091_ = v_reuseFailAlloc_3092_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg___boxed(
    mut v_x_3094_: *mut crate::leanh::LeanObject,
    mut v_state_3095_: *mut crate::leanh::LeanObject,
    mut v_ctx_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
    mut v_a_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
    mut v_a_3100_: *mut crate::leanh::LeanObject,
    mut v_a_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctx_boxed_3102_: u8 = 0;
    let mut v_res_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_3102_ = (crate::leanh::lean_unbox(v_ctx_3096_) as u8);
    v_res_3103_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(
        v_x_3094_,
        v_state_3095_,
        v_ctx_boxed_3102_,
        v_a_3097_,
        v_a_3098_,
        v_a_3099_,
        v_a_3100_,
    );
    crate::leanh::lean_dec(v_a_3100_);
    crate::leanh::lean_dec_ref(v_a_3099_);
    crate::leanh::lean_dec(v_a_3098_);
    crate::leanh::lean_dec_ref(v_a_3097_);
    return v_res_3103_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(
    mut v_pu_3104_: u8,
    mut v_00_u03b1_3105_: *mut crate::leanh::LeanObject,
    mut v_x_3106_: *mut crate::leanh::LeanObject,
    mut v_state_3107_: *mut crate::leanh::LeanObject,
    mut v_ctx_3108_: u8,
    mut v_a_3109_: *mut crate::leanh::LeanObject,
    mut v_a_3110_: *mut crate::leanh::LeanObject,
    mut v_a_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_a_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3114_ = lean_st_mk_ref(v_state_3107_);
                v___x_3115_ = crate::leanh::lean_box((v_ctx_3108_) as usize);
                crate::leanh::lean_inc(v_a_3112_);
                crate::leanh::lean_inc_ref(v_a_3111_);
                crate::leanh::lean_inc(v_a_3110_);
                crate::leanh::lean_inc_ref(v_a_3109_);
                crate::leanh::lean_inc(v___x_3114_);
                v___x_3116_ = crate::leanh::lean_apply_7(
                    v_x_3106_,
                    v___x_3115_,
                    v___x_3114_,
                    v_a_3109_,
                    v_a_3110_,
                    v_a_3111_,
                    v_a_3112_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3116_) == 0 {
                    v_a_3117_ = crate::leanh::lean_ctor_get(v___x_3116_, 0);
                    v_isSharedCheck_3126_ = (!crate::leanh::lean_is_exclusive(v___x_3116_)) as u8;
                    if v_isSharedCheck_3126_ == 0 {
                        v___x_3119_ = v___x_3116_;
                        v_isShared_3120_ = v_isSharedCheck_3126_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3117_);
                        crate::leanh::lean_dec(v___x_3116_);
                        v___x_3119_ = crate::leanh::lean_box(0);
                        v_isShared_3120_ = v_isSharedCheck_3126_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3114_);
                    v_a_3127_ = crate::leanh::lean_ctor_get(v___x_3116_, 0);
                    v_isSharedCheck_3134_ = (!crate::leanh::lean_is_exclusive(v___x_3116_)) as u8;
                    if v_isSharedCheck_3134_ == 0 {
                        v___x_3129_ = v___x_3116_;
                        v_isShared_3130_ = v_isSharedCheck_3134_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3127_);
                        crate::leanh::lean_dec(v___x_3116_);
                        v___x_3129_ = crate::leanh::lean_box(0);
                        v_isShared_3130_ = v_isSharedCheck_3134_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3121_ = lean_st_ref_get(v___x_3114_);
                crate::leanh::lean_dec(v___x_3114_);
                v___x_3122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3122_, 0, v_a_3117_);
                crate::leanh::lean_ctor_set(v___x_3122_, 1, v___x_3121_);
                if v_isShared_3120_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3119_, 0, v___x_3122_);
                    v___x_3124_ = v___x_3119_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
                    v___x_3124_ = v_reuseFailAlloc_3125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3124_;
            }
            3 => {
                if v_isShared_3130_ == 0 {
                    v___x_3132_ = v___x_3129_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
                    v___x_3132_ = v_reuseFailAlloc_3133_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___boxed(
    mut v_pu_3135_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3136_: *mut crate::leanh::LeanObject,
    mut v_x_3137_: *mut crate::leanh::LeanObject,
    mut v_state_3138_: *mut crate::leanh::LeanObject,
    mut v_ctx_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
    mut v_a_3143_: *mut crate::leanh::LeanObject,
    mut v_a_3144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3145_: u8 = 0;
    let mut v_ctx_boxed_3146_: u8 = 0;
    let mut v_res_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3145_ = (crate::leanh::lean_unbox(v_pu_3135_) as u8);
    v_ctx_boxed_3146_ = (crate::leanh::lean_unbox(v_ctx_3139_) as u8);
    v_res_3147_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(
        v_pu_boxed_3145_,
        v_00_u03b1_3136_,
        v_x_3137_,
        v_state_3138_,
        v_ctx_boxed_3146_,
        v_a_3140_,
        v_a_3141_,
        v_a_3142_,
        v_a_3143_,
    );
    crate::leanh::lean_dec(v_a_3143_);
    crate::leanh::lean_dec_ref(v_a_3142_);
    crate::leanh::lean_dec(v_a_3141_);
    crate::leanh::lean_dec_ref(v_a_3140_);
    return v_res_3147_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(
    mut v_x_3148_: *mut crate::leanh::LeanObject,
    mut v_state_3149_: *mut crate::leanh::LeanObject,
    mut v_ctx_3150_: u8,
    mut v_a_3151_: *mut crate::leanh::LeanObject,
    mut v_a_3152_: *mut crate::leanh::LeanObject,
    mut v_a_3153_: *mut crate::leanh::LeanObject,
    mut v_a_3154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3162_: u8 = 0;
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3156_ = lean_st_mk_ref(v_state_3149_);
                v___x_3157_ = crate::leanh::lean_box((v_ctx_3150_) as usize);
                crate::leanh::lean_inc(v_a_3154_);
                crate::leanh::lean_inc_ref(v_a_3153_);
                crate::leanh::lean_inc(v_a_3152_);
                crate::leanh::lean_inc_ref(v_a_3151_);
                crate::leanh::lean_inc(v___x_3156_);
                v___x_3158_ = crate::leanh::lean_apply_7(
                    v_x_3148_,
                    v___x_3157_,
                    v___x_3156_,
                    v_a_3151_,
                    v_a_3152_,
                    v_a_3153_,
                    v_a_3154_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3158_) == 0 {
                    v_a_3159_ = crate::leanh::lean_ctor_get(v___x_3158_, 0);
                    v_isSharedCheck_3167_ = (!crate::leanh::lean_is_exclusive(v___x_3158_)) as u8;
                    if v_isSharedCheck_3167_ == 0 {
                        v___x_3161_ = v___x_3158_;
                        v_isShared_3162_ = v_isSharedCheck_3167_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3159_);
                        crate::leanh::lean_dec(v___x_3158_);
                        v___x_3161_ = crate::leanh::lean_box(0);
                        v_isShared_3162_ = v_isSharedCheck_3167_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3156_);
                    return v___x_3158_;
                }
            }
            1 => {
                v___x_3163_ = lean_st_ref_get(v___x_3156_);
                crate::leanh::lean_dec(v___x_3156_);
                crate::leanh::lean_dec(v___x_3163_);
                if v_isShared_3162_ == 0 {
                    v___x_3165_ = v___x_3161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3166_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3159_);
                    v___x_3165_ = v_reuseFailAlloc_3166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg___boxed(
    mut v_x_3168_: *mut crate::leanh::LeanObject,
    mut v_state_3169_: *mut crate::leanh::LeanObject,
    mut v_ctx_3170_: *mut crate::leanh::LeanObject,
    mut v_a_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
    mut v_a_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctx_boxed_3176_: u8 = 0;
    let mut v_res_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_3176_ = (crate::leanh::lean_unbox(v_ctx_3170_) as u8);
    v_res_3177_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(
        v_x_3168_,
        v_state_3169_,
        v_ctx_boxed_3176_,
        v_a_3171_,
        v_a_3172_,
        v_a_3173_,
        v_a_3174_,
    );
    crate::leanh::lean_dec(v_a_3174_);
    crate::leanh::lean_dec_ref(v_a_3173_);
    crate::leanh::lean_dec(v_a_3172_);
    crate::leanh::lean_dec_ref(v_a_3171_);
    return v_res_3177_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(
    mut v_pu_3178_: u8,
    mut v_00_u03b1_3179_: *mut crate::leanh::LeanObject,
    mut v_x_3180_: *mut crate::leanh::LeanObject,
    mut v_state_3181_: *mut crate::leanh::LeanObject,
    mut v_ctx_3182_: u8,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_a_3185_: *mut crate::leanh::LeanObject,
    mut v_a_3186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3188_ = lean_st_mk_ref(v_state_3181_);
                v___x_3189_ = crate::leanh::lean_box((v_ctx_3182_) as usize);
                crate::leanh::lean_inc(v_a_3186_);
                crate::leanh::lean_inc_ref(v_a_3185_);
                crate::leanh::lean_inc(v_a_3184_);
                crate::leanh::lean_inc_ref(v_a_3183_);
                crate::leanh::lean_inc(v___x_3188_);
                v___x_3190_ = crate::leanh::lean_apply_7(
                    v_x_3180_,
                    v___x_3189_,
                    v___x_3188_,
                    v_a_3183_,
                    v_a_3184_,
                    v_a_3185_,
                    v_a_3186_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3190_) == 0 {
                    v_a_3191_ = crate::leanh::lean_ctor_get(v___x_3190_, 0);
                    v_isSharedCheck_3199_ = (!crate::leanh::lean_is_exclusive(v___x_3190_)) as u8;
                    if v_isSharedCheck_3199_ == 0 {
                        v___x_3193_ = v___x_3190_;
                        v_isShared_3194_ = v_isSharedCheck_3199_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3191_);
                        crate::leanh::lean_dec(v___x_3190_);
                        v___x_3193_ = crate::leanh::lean_box(0);
                        v_isShared_3194_ = v_isSharedCheck_3199_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3188_);
                    return v___x_3190_;
                }
            }
            1 => {
                v___x_3195_ = lean_st_ref_get(v___x_3188_);
                crate::leanh::lean_dec(v___x_3188_);
                crate::leanh::lean_dec(v___x_3195_);
                if v_isShared_3194_ == 0 {
                    v___x_3197_ = v___x_3193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3191_);
                    v___x_3197_ = v_reuseFailAlloc_3198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___boxed(
    mut v_pu_3200_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3201_: *mut crate::leanh::LeanObject,
    mut v_x_3202_: *mut crate::leanh::LeanObject,
    mut v_state_3203_: *mut crate::leanh::LeanObject,
    mut v_ctx_3204_: *mut crate::leanh::LeanObject,
    mut v_a_3205_: *mut crate::leanh::LeanObject,
    mut v_a_3206_: *mut crate::leanh::LeanObject,
    mut v_a_3207_: *mut crate::leanh::LeanObject,
    mut v_a_3208_: *mut crate::leanh::LeanObject,
    mut v_a_3209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3210_: u8 = 0;
    let mut v_ctx_boxed_3211_: u8 = 0;
    let mut v_res_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3210_ = (crate::leanh::lean_unbox(v_pu_3200_) as u8);
    v_ctx_boxed_3211_ = (crate::leanh::lean_unbox(v_ctx_3204_) as u8);
    v_res_3212_ = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(
        v_pu_boxed_3210_,
        v_00_u03b1_3201_,
        v_x_3202_,
        v_state_3203_,
        v_ctx_boxed_3211_,
        v_a_3205_,
        v_a_3206_,
        v_a_3207_,
        v_a_3208_,
    );
    crate::leanh::lean_dec(v_a_3208_);
    crate::leanh::lean_dec_ref(v_a_3207_);
    crate::leanh::lean_dec(v_a_3206_);
    crate::leanh::lean_dec_ref(v_a_3205_);
    return v_res_3212_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(
    mut v_binderName_3213_: *mut crate::leanh::LeanObject,
    mut v_a_3214_: u8,
    mut v_a_3215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pre_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3223_: u8 = 0;
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3239_: u8 = 0;
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_binderName_3213_) == 2 {
                    v_pre_3217_ = crate::leanh::lean_ctor_get(v_binderName_3213_, 0);
                    crate::leanh::lean_inc(v_pre_3217_);
                    crate::leanh::lean_dec_ref_known(v_binderName_3213_, 2);
                    v___x_3218_ = lean_st_ref_take(v_a_3215_);
                    v_lctx_3219_ = crate::leanh::lean_ctor_get(v___x_3218_, 0);
                    v_nextIdx_3220_ = crate::leanh::lean_ctor_get(v___x_3218_, 1);
                    v_isSharedCheck_3232_ = (!crate::leanh::lean_is_exclusive(v___x_3218_)) as u8;
                    if v_isSharedCheck_3232_ == 0 {
                        v___x_3222_ = v___x_3218_;
                        v_isShared_3223_ = v_isSharedCheck_3232_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_nextIdx_3220_);
                        crate::leanh::lean_inc(v_lctx_3219_);
                        crate::leanh::lean_dec(v___x_3218_);
                        v___x_3222_ = crate::leanh::lean_box(0);
                        v_isShared_3223_ = v_isSharedCheck_3232_;
                        state = 1;
                        continue;
                    }
                } else {
                    if v_a_3214_ == 0 {
                        v___x_3233_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3233_, 0, v_binderName_3213_);
                        return v___x_3233_;
                    } else {
                        v___x_3234_ = lean_st_ref_take(v_a_3215_);
                        v_lctx_3235_ = crate::leanh::lean_ctor_get(v___x_3234_, 0);
                        v_nextIdx_3236_ = crate::leanh::lean_ctor_get(v___x_3234_, 1);
                        v_isSharedCheck_3248_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3234_)) as u8;
                        if v_isSharedCheck_3248_ == 0 {
                            v___x_3238_ = v___x_3234_;
                            v_isShared_3239_ = v_isSharedCheck_3248_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_nextIdx_3236_);
                            crate::leanh::lean_inc(v_lctx_3235_);
                            crate::leanh::lean_dec(v___x_3234_);
                            v___x_3238_ = crate::leanh::lean_box(0);
                            v_isShared_3239_ = v_isSharedCheck_3248_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3224_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3225_ = lean_nat_add(v_nextIdx_3220_, v___x_3224_);
                if v_isShared_3223_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3222_, 1, v___x_3225_);
                    v___x_3227_ = v___x_3222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_lctx_3219_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3225_);
                    v___x_3227_ = v_reuseFailAlloc_3231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3228_ = lean_st_ref_set(v_a_3215_, v___x_3227_);
                v___x_3229_ = l_Lean_Name_num___override(v_pre_3217_, v_nextIdx_3220_);
                v___x_3230_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3230_, 0, v___x_3229_);
                return v___x_3230_;
            }
            3 => {
                v___x_3240_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3241_ = lean_nat_add(v_nextIdx_3236_, v___x_3240_);
                if v_isShared_3239_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3238_, 1, v___x_3241_);
                    v___x_3243_ = v___x_3238_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3247_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_lctx_3235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 1, v___x_3241_);
                    v___x_3243_ = v_reuseFailAlloc_3247_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3244_ = lean_st_ref_set(v_a_3215_, v___x_3243_);
                v___x_3245_ = l_Lean_Name_num___override(v_binderName_3213_, v_nextIdx_3236_);
                v___x_3246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3246_, 0, v___x_3245_);
                return v___x_3246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg___boxed(
    mut v_binderName_3249_: *mut crate::leanh::LeanObject,
    mut v_a_3250_: *mut crate::leanh::LeanObject,
    mut v_a_3251_: *mut crate::leanh::LeanObject,
    mut v_a_3252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3253_: u8 = 0;
    let mut v_res_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3253_ = (crate::leanh::lean_unbox(v_a_3250_) as u8);
    v_res_3254_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_3249_, v_a_boxed_3253_, v_a_3251_);
    crate::leanh::lean_dec(v_a_3251_);
    return v_res_3254_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(
    mut v_pu_3255_: u8,
    mut v_binderName_3256_: *mut crate::leanh::LeanObject,
    mut v_a_3257_: u8,
    mut v_a_3258_: *mut crate::leanh::LeanObject,
    mut v_a_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
    mut v_a_3262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3264_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_3256_, v_a_3257_, v_a_3260_);
    return v___x_3264_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___boxed(
    mut v_pu_3265_: *mut crate::leanh::LeanObject,
    mut v_binderName_3266_: *mut crate::leanh::LeanObject,
    mut v_a_3267_: *mut crate::leanh::LeanObject,
    mut v_a_3268_: *mut crate::leanh::LeanObject,
    mut v_a_3269_: *mut crate::leanh::LeanObject,
    mut v_a_3270_: *mut crate::leanh::LeanObject,
    mut v_a_3271_: *mut crate::leanh::LeanObject,
    mut v_a_3272_: *mut crate::leanh::LeanObject,
    mut v_a_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3274_: u8 = 0;
    let mut v_a_boxed_3275_: u8 = 0;
    let mut v_res_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3274_ = (crate::leanh::lean_unbox(v_pu_3265_) as u8);
    v_a_boxed_3275_ = (crate::leanh::lean_unbox(v_a_3267_) as u8);
    v_res_3276_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(v_pu_boxed_3274_, v_binderName_3266_, v_a_boxed_3275_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
    crate::leanh::lean_dec(v_a_3272_);
    crate::leanh::lean_dec_ref(v_a_3271_);
    crate::leanh::lean_dec(v_a_3270_);
    crate::leanh::lean_dec_ref(v_a_3269_);
    crate::leanh::lean_dec(v_a_3268_);
    return v_res_3276_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0(
    mut v___y_3277_: u8,
    mut v___y_3278_: *mut crate::leanh::LeanObject,
    mut v___y_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3284_ = lean_st_ref_get(v___y_3278_);
    v___x_3285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3285_, 0, v___x_3284_);
    return v___x_3285_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0___boxed(
    mut v___y_3286_: *mut crate::leanh::LeanObject,
    mut v___y_3287_: *mut crate::leanh::LeanObject,
    mut v___y_3288_: *mut crate::leanh::LeanObject,
    mut v___y_3289_: *mut crate::leanh::LeanObject,
    mut v___y_3290_: *mut crate::leanh::LeanObject,
    mut v___y_3291_: *mut crate::leanh::LeanObject,
    mut v___y_3292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_198__boxed_3293_: u8 = 0;
    let mut v_res_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_198__boxed_3293_ = (crate::leanh::lean_unbox(v___y_3286_) as u8);
    v_res_3294_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0(
        v___y_198__boxed_3293_,
        v___y_3287_,
        v___y_3288_,
        v___y_3289_,
        v___y_3290_,
        v___y_3291_,
    );
    crate::leanh::lean_dec(v___y_3291_);
    crate::leanh::lean_dec_ref(v___y_3290_);
    crate::leanh::lean_dec(v___y_3289_);
    crate::leanh::lean_dec_ref(v___y_3288_);
    crate::leanh::lean_dec(v___y_3287_);
    return v_res_3294_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(
    mut v_pu_3296_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3297_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0;
    return v___f_3297_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___boxed(
    mut v_pu_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3299_: u8 = 0;
    let mut v_res_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3299_ = (crate::leanh::lean_unbox(v_pu_3298_) as u8);
    v_res_3300_ =
        l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(v_pu_boxed_3299_);
    return v_res_3300_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3322_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10;
    v___x_3323_ = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(v___f_3322_);
    return v___x_3323_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(
    mut v_pu_3324_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3325_ = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0;
    v___x_3326_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11_once
        ),
        _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11,
    );
    v_get_3327_ = crate::leanh::lean_ctor_get(v___x_3326_, 0);
    v_set_3328_ = crate::leanh::lean_ctor_get(v___x_3326_, 1);
    v_modifyGet_3329_ = crate::leanh::lean_ctor_get(v___x_3326_, 2);
    crate::leanh::lean_inc(v_set_3328_);
    v___f_3330_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3330_, 0, v_set_3328_);
    crate::leanh::lean_closure_set(v___f_3330_, 1, v___f_3325_);
    crate::leanh::lean_inc(v_modifyGet_3329_);
    v___f_3331_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3331_, 0, v_modifyGet_3329_);
    crate::leanh::lean_closure_set(v___f_3331_, 1, v___f_3325_);
    crate::leanh::lean_inc(v_get_3327_);
    v___x_3332_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadLift___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3332_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3332_, 1, v_get_3327_);
    v___x_3333_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3333_, 0, v___x_3332_);
    crate::leanh::lean_ctor_set(v___x_3333_, 1, v___f_3330_);
    crate::leanh::lean_ctor_set(v___x_3333_, 2, v___f_3331_);
    v___x_3334_ = l_instMonadStateOfMonadStateOf___redArg(v___x_3333_);
    v___x_3335_ = crate::leanh::lean_alloc_closure(l_modify as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_3335_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3335_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3335_, 2, v___x_3334_);
    return v___x_3335_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___boxed(
    mut v_pu_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3337_: u8 = 0;
    let mut v_res_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3337_ = (crate::leanh::lean_unbox(v_pu_3336_) as u8);
    v_res_3338_ =
        l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(v_pu_boxed_3337_);
    return v_res_3338_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(
    mut v_a_3339_: *mut crate::leanh::LeanObject,
    mut v_x_3340_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3341_: u8 = 0;
    let mut v_key_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3340_) == 0 {
                    v___x_3341_ = 0;
                    return v___x_3341_;
                } else {
                    v_key_3342_ = crate::leanh::lean_ctor_get(v_x_3340_, 0);
                    v_tail_3343_ = crate::leanh::lean_ctor_get(v_x_3340_, 2);
                    v___x_3344_ = l_Lean_instBEqFVarId_beq(v_key_3342_, v_a_3339_);
                    if v___x_3344_ == 0 {
                        v_x_3340_ = v_tail_3343_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3344_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_x_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3348_: u8 = 0;
    let mut v_r_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3348_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_3346_, v_x_3347_);
    crate::leanh::lean_dec(v_x_3347_);
    crate::leanh::lean_dec(v_a_3346_);
    v_r_3349_ = crate::leanh::lean_box((v_res_3348_) as usize);
    return v_r_3349_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(
    mut v_a_3350_: *mut crate::leanh::LeanObject,
    mut v_b_3351_: *mut crate::leanh::LeanObject,
    mut v_x_3352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3358_: u8 = 0;
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3352_) == 0 {
                    crate::leanh::lean_dec(v_b_3351_);
                    crate::leanh::lean_dec(v_a_3350_);
                    return v_x_3352_;
                } else {
                    v_key_3353_ = crate::leanh::lean_ctor_get(v_x_3352_, 0);
                    v_value_3354_ = crate::leanh::lean_ctor_get(v_x_3352_, 1);
                    v_tail_3355_ = crate::leanh::lean_ctor_get(v_x_3352_, 2);
                    v_isSharedCheck_3367_ = (!crate::leanh::lean_is_exclusive(v_x_3352_)) as u8;
                    if v_isSharedCheck_3367_ == 0 {
                        v___x_3357_ = v_x_3352_;
                        v_isShared_3358_ = v_isSharedCheck_3367_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3355_);
                        crate::leanh::lean_inc(v_value_3354_);
                        crate::leanh::lean_inc(v_key_3353_);
                        crate::leanh::lean_dec(v_x_3352_);
                        v___x_3357_ = crate::leanh::lean_box(0);
                        v_isShared_3358_ = v_isSharedCheck_3367_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3359_ = l_Lean_instBEqFVarId_beq(v_key_3353_, v_a_3350_);
                if v___x_3359_ == 0 {
                    v___x_3360_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_3350_, v_b_3351_, v_tail_3355_);
                    if v_isShared_3358_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3357_, 2, v___x_3360_);
                        v___x_3362_ = v___x_3357_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3363_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_key_3353_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_value_3354_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 2, v___x_3360_);
                        v___x_3362_ = v_reuseFailAlloc_3363_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3354_);
                    crate::leanh::lean_dec(v_key_3353_);
                    if v_isShared_3358_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3357_, 1, v_b_3351_);
                        crate::leanh::lean_ctor_set(v___x_3357_, 0, v_a_3350_);
                        v___x_3365_ = v___x_3357_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3366_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3350_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_b_3351_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 2, v_tail_3355_);
                        v___x_3365_ = v_reuseFailAlloc_3366_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3362_;
            }
            3 => {
                return v___x_3365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_3368_: *mut crate::leanh::LeanObject,
    mut v_x_3369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3375_: u8 = 0;
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: u64 = 0;
    let mut v___x_3378_: u64 = 0;
    let mut v___x_3379_: u64 = 0;
    let mut v_fold_3380_: u64 = 0;
    let mut v___x_3381_: u64 = 0;
    let mut v___x_3382_: u64 = 0;
    let mut v___x_3383_: u64 = 0;
    let mut v___x_3384_: usize = 0;
    let mut v___x_3385_: usize = 0;
    let mut v___x_3386_: usize = 0;
    let mut v___x_3387_: usize = 0;
    let mut v___x_3388_: usize = 0;
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3369_) == 0 {
                    return v_x_3368_;
                } else {
                    v_key_3370_ = crate::leanh::lean_ctor_get(v_x_3369_, 0);
                    v_value_3371_ = crate::leanh::lean_ctor_get(v_x_3369_, 1);
                    v_tail_3372_ = crate::leanh::lean_ctor_get(v_x_3369_, 2);
                    v_isSharedCheck_3395_ = (!crate::leanh::lean_is_exclusive(v_x_3369_)) as u8;
                    if v_isSharedCheck_3395_ == 0 {
                        v___x_3374_ = v_x_3369_;
                        v_isShared_3375_ = v_isSharedCheck_3395_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3372_);
                        crate::leanh::lean_inc(v_value_3371_);
                        crate::leanh::lean_inc(v_key_3370_);
                        crate::leanh::lean_dec(v_x_3369_);
                        v___x_3374_ = crate::leanh::lean_box(0);
                        v_isShared_3375_ = v_isSharedCheck_3395_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3376_ = lean_array_get_size(v_x_3368_);
                v___x_3377_ = l_Lean_instHashableFVarId_hash(v_key_3370_);
                v___x_3378_ = 32u64;
                v___x_3379_ = lean_uint64_shift_right(v___x_3377_, v___x_3378_);
                v_fold_3380_ = lean_uint64_xor(v___x_3377_, v___x_3379_);
                v___x_3381_ = 16u64;
                v___x_3382_ = lean_uint64_shift_right(v_fold_3380_, v___x_3381_);
                v___x_3383_ = lean_uint64_xor(v_fold_3380_, v___x_3382_);
                v___x_3384_ = lean_uint64_to_usize(v___x_3383_);
                v___x_3385_ = lean_usize_of_nat(v___x_3376_);
                v___x_3386_ = 1usize;
                v___x_3387_ = lean_usize_sub(v___x_3385_, v___x_3386_);
                v___x_3388_ = lean_usize_land(v___x_3384_, v___x_3387_);
                v___x_3389_ = lean_array_uget_borrowed(v_x_3368_, v___x_3388_);
                crate::leanh::lean_inc(v___x_3389_);
                if v_isShared_3375_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3374_, 2, v___x_3389_);
                    v___x_3391_ = v___x_3374_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3394_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_key_3370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_value_3371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3394_, 2, v___x_3389_);
                    v___x_3391_ = v_reuseFailAlloc_3394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3392_ = lean_array_uset(v_x_3368_, v___x_3388_, v___x_3391_);
                v_x_3368_ = v___x_3392_;
                v_x_3369_ = v_tail_3372_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(
    mut v_i_3396_: *mut crate::leanh::LeanObject,
    mut v_source_3397_: *mut crate::leanh::LeanObject,
    mut v_target_3398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    let mut v_es_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3399_ = lean_array_get_size(v_source_3397_);
                v___x_3400_ = lean_nat_dec_lt(v_i_3396_, v___x_3399_);
                if v___x_3400_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3397_);
                    crate::leanh::lean_dec(v_i_3396_);
                    return v_target_3398_;
                } else {
                    v_es_3401_ = lean_array_fget(v_source_3397_, v_i_3396_);
                    v___x_3402_ = crate::leanh::lean_box(0);
                    v_source_3403_ = lean_array_fset(v_source_3397_, v_i_3396_, v___x_3402_);
                    v_target_3404_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_target_3398_, v_es_3401_);
                    v___x_3405_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3406_ = lean_nat_add(v_i_3396_, v___x_3405_);
                    crate::leanh::lean_dec(v_i_3396_);
                    v_i_3396_ = v___x_3406_;
                    v_source_3397_ = v_source_3403_;
                    v_target_3398_ = v_target_3404_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(
    mut v_data_3408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ = lean_array_get_size(v_data_3408_);
    v___x_3410_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3411_ = lean_nat_mul(v___x_3409_, v___x_3410_);
    v___x_3412_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3413_ = crate::leanh::lean_box(0);
    v___x_3414_ = lean_mk_array(v_nbuckets_3411_, v___x_3413_);
    v___x_3415_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v___x_3412_, v_data_3408_, v___x_3414_);
    return v___x_3415_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(
    mut v_m_3416_: *mut crate::leanh::LeanObject,
    mut v_a_3417_: *mut crate::leanh::LeanObject,
    mut v_b_3418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3423_: u8 = 0;
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: u64 = 0;
    let mut v___x_3426_: u64 = 0;
    let mut v___x_3427_: u64 = 0;
    let mut v_fold_3428_: u64 = 0;
    let mut v___x_3429_: u64 = 0;
    let mut v___x_3430_: u64 = 0;
    let mut v___x_3431_: u64 = 0;
    let mut v___x_3432_: usize = 0;
    let mut v___x_3433_: usize = 0;
    let mut v___x_3434_: usize = 0;
    let mut v___x_3435_: usize = 0;
    let mut v___x_3436_: usize = 0;
    let mut v_bkt_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: u8 = 0;
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v_val_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3419_ = crate::leanh::lean_ctor_get(v_m_3416_, 0);
                v_buckets_3420_ = crate::leanh::lean_ctor_get(v_m_3416_, 1);
                v_isSharedCheck_3463_ = (!crate::leanh::lean_is_exclusive(v_m_3416_)) as u8;
                if v_isSharedCheck_3463_ == 0 {
                    v___x_3422_ = v_m_3416_;
                    v_isShared_3423_ = v_isSharedCheck_3463_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3420_);
                    crate::leanh::lean_inc(v_size_3419_);
                    crate::leanh::lean_dec(v_m_3416_);
                    v___x_3422_ = crate::leanh::lean_box(0);
                    v_isShared_3423_ = v_isSharedCheck_3463_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3424_ = lean_array_get_size(v_buckets_3420_);
                v___x_3425_ = l_Lean_instHashableFVarId_hash(v_a_3417_);
                v___x_3426_ = 32u64;
                v___x_3427_ = lean_uint64_shift_right(v___x_3425_, v___x_3426_);
                v_fold_3428_ = lean_uint64_xor(v___x_3425_, v___x_3427_);
                v___x_3429_ = 16u64;
                v___x_3430_ = lean_uint64_shift_right(v_fold_3428_, v___x_3429_);
                v___x_3431_ = lean_uint64_xor(v_fold_3428_, v___x_3430_);
                v___x_3432_ = lean_uint64_to_usize(v___x_3431_);
                v___x_3433_ = lean_usize_of_nat(v___x_3424_);
                v___x_3434_ = 1usize;
                v___x_3435_ = lean_usize_sub(v___x_3433_, v___x_3434_);
                v___x_3436_ = lean_usize_land(v___x_3432_, v___x_3435_);
                v_bkt_3437_ = lean_array_uget_borrowed(v_buckets_3420_, v___x_3436_);
                v___x_3438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_3417_, v_bkt_3437_);
                if v___x_3438_ == 0 {
                    v___x_3439_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3440_ = lean_nat_add(v_size_3419_, v___x_3439_);
                    crate::leanh::lean_dec(v_size_3419_);
                    crate::leanh::lean_inc(v_bkt_3437_);
                    v___x_3441_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3441_, 0, v_a_3417_);
                    crate::leanh::lean_ctor_set(v___x_3441_, 1, v_b_3418_);
                    crate::leanh::lean_ctor_set(v___x_3441_, 2, v_bkt_3437_);
                    v_buckets_x27_3442_ =
                        lean_array_uset(v_buckets_3420_, v___x_3436_, v___x_3441_);
                    v___x_3443_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3444_ = lean_nat_mul(v_size_x27_3440_, v___x_3443_);
                    v___x_3445_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3446_ = lean_nat_div(v___x_3444_, v___x_3445_);
                    crate::leanh::lean_dec(v___x_3444_);
                    v___x_3447_ = lean_array_get_size(v_buckets_x27_3442_);
                    v___x_3448_ = lean_nat_dec_le(v___x_3446_, v___x_3447_);
                    crate::leanh::lean_dec(v___x_3446_);
                    if v___x_3448_ == 0 {
                        v_val_3449_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_buckets_x27_3442_);
                        if v_isShared_3423_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3422_, 1, v_val_3449_);
                            crate::leanh::lean_ctor_set(v___x_3422_, 0, v_size_x27_3440_);
                            v___x_3451_ = v___x_3422_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3452_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3452_,
                                0,
                                v_size_x27_3440_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_val_3449_);
                            v___x_3451_ = v_reuseFailAlloc_3452_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3423_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3422_, 1, v_buckets_x27_3442_);
                            crate::leanh::lean_ctor_set(v___x_3422_, 0, v_size_x27_3440_);
                            v___x_3454_ = v___x_3422_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3455_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3455_,
                                0,
                                v_size_x27_3440_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3455_,
                                1,
                                v_buckets_x27_3442_,
                            );
                            v___x_3454_ = v_reuseFailAlloc_3455_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3437_);
                    v___x_3456_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3457_ =
                        lean_array_uset(v_buckets_3420_, v___x_3436_, v___x_3456_);
                    v___x_3458_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_3417_, v_b_3418_, v_bkt_3437_);
                    v___x_3459_ = lean_array_uset(v_buckets_x27_3457_, v___x_3436_, v___x_3458_);
                    if v_isShared_3423_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3422_, 1, v___x_3459_);
                        v___x_3461_ = v___x_3422_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3462_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_size_3419_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 1, v___x_3459_);
                        v___x_3461_ = v_reuseFailAlloc_3462_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3451_;
            }
            3 => {
                return v___x_3454_;
            }
            4 => {
                return v___x_3461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(
    mut v___y_3464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3472_: u8 = 0;
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v_r_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut v_unused_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3466_ = lean_st_ref_get(v___y_3464_);
                v_ngen_3467_ = crate::leanh::lean_ctor_get(v___x_3466_, 2);
                crate::leanh::lean_inc_ref(v_ngen_3467_);
                crate::leanh::lean_dec(v___x_3466_);
                v_namePrefix_3468_ = crate::leanh::lean_ctor_get(v_ngen_3467_, 0);
                v_idx_3469_ = crate::leanh::lean_ctor_get(v_ngen_3467_, 1);
                v_isSharedCheck_3498_ = (!crate::leanh::lean_is_exclusive(v_ngen_3467_)) as u8;
                if v_isSharedCheck_3498_ == 0 {
                    v___x_3471_ = v_ngen_3467_;
                    v_isShared_3472_ = v_isSharedCheck_3498_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_3469_);
                    crate::leanh::lean_inc(v_namePrefix_3468_);
                    crate::leanh::lean_dec(v_ngen_3467_);
                    v___x_3471_ = crate::leanh::lean_box(0);
                    v_isShared_3472_ = v_isSharedCheck_3498_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3473_ = lean_st_ref_take(v___y_3464_);
                v_env_3474_ = crate::leanh::lean_ctor_get(v___x_3473_, 0);
                v_nextMacroScope_3475_ = crate::leanh::lean_ctor_get(v___x_3473_, 1);
                v_auxDeclNGen_3476_ = crate::leanh::lean_ctor_get(v___x_3473_, 3);
                v_traceState_3477_ = crate::leanh::lean_ctor_get(v___x_3473_, 4);
                v_cache_3478_ = crate::leanh::lean_ctor_get(v___x_3473_, 5);
                v_messages_3479_ = crate::leanh::lean_ctor_get(v___x_3473_, 6);
                v_infoState_3480_ = crate::leanh::lean_ctor_get(v___x_3473_, 7);
                v_snapshotTasks_3481_ = crate::leanh::lean_ctor_get(v___x_3473_, 8);
                v_isSharedCheck_3496_ = (!crate::leanh::lean_is_exclusive(v___x_3473_)) as u8;
                if v_isSharedCheck_3496_ == 0 {
                    v_unused_3497_ = crate::leanh::lean_ctor_get(v___x_3473_, 2);
                    crate::leanh::lean_dec(v_unused_3497_);
                    v___x_3483_ = v___x_3473_;
                    v_isShared_3484_ = v_isSharedCheck_3496_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3481_);
                    crate::leanh::lean_inc(v_infoState_3480_);
                    crate::leanh::lean_inc(v_messages_3479_);
                    crate::leanh::lean_inc(v_cache_3478_);
                    crate::leanh::lean_inc(v_traceState_3477_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3476_);
                    crate::leanh::lean_inc(v_nextMacroScope_3475_);
                    crate::leanh::lean_inc(v_env_3474_);
                    crate::leanh::lean_dec(v___x_3473_);
                    v___x_3483_ = crate::leanh::lean_box(0);
                    v_isShared_3484_ = v_isSharedCheck_3496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_3469_);
                crate::leanh::lean_inc(v_namePrefix_3468_);
                v_r_3485_ = l_Lean_Name_num___override(v_namePrefix_3468_, v_idx_3469_);
                v___x_3486_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3487_ = lean_nat_add(v_idx_3469_, v___x_3486_);
                crate::leanh::lean_dec(v_idx_3469_);
                if v_isShared_3472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3471_, 1, v___x_3487_);
                    v___x_3489_ = v___x_3471_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_namePrefix_3468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 1, v___x_3487_);
                    v___x_3489_ = v_reuseFailAlloc_3495_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3483_, 2, v___x_3489_);
                    v___x_3491_ = v___x_3483_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_env_3474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_nextMacroScope_3475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 2, v___x_3489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 3, v_auxDeclNGen_3476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 4, v_traceState_3477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 5, v_cache_3478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 6, v_messages_3479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 7, v_infoState_3480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 8, v_snapshotTasks_3481_);
                    v___x_3491_ = v_reuseFailAlloc_3494_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3492_ = lean_st_ref_set(v___y_3464_, v___x_3491_);
                v___x_3493_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3493_, 0, v_r_3485_);
                return v___x_3493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3501_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_3499_);
    crate::leanh::lean_dec(v___y_3499_);
    return v_res_3501_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(
    mut v___y_3502_: u8,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
    mut v___y_3504_: *mut crate::leanh::LeanObject,
    mut v___y_3505_: *mut crate::leanh::LeanObject,
    mut v___y_3506_: *mut crate::leanh::LeanObject,
    mut v___y_3507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3513_: u8 = 0;
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3509_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_3507_);
                v_a_3510_ = crate::leanh::lean_ctor_get(v___x_3509_, 0);
                v_isSharedCheck_3517_ = (!crate::leanh::lean_is_exclusive(v___x_3509_)) as u8;
                if v_isSharedCheck_3517_ == 0 {
                    v___x_3512_ = v___x_3509_;
                    v_isShared_3513_ = v_isSharedCheck_3517_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3510_);
                    crate::leanh::lean_dec(v___x_3509_);
                    v___x_3512_ = crate::leanh::lean_box(0);
                    v_isShared_3513_ = v_isSharedCheck_3517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3513_ == 0 {
                    v___x_3515_ = v___x_3512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
                    v___x_3515_ = v_reuseFailAlloc_3516_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(
    mut v___y_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
    mut v___y_3520_: *mut crate::leanh::LeanObject,
    mut v___y_3521_: *mut crate::leanh::LeanObject,
    mut v___y_3522_: *mut crate::leanh::LeanObject,
    mut v___y_3523_: *mut crate::leanh::LeanObject,
    mut v___y_3524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3107__boxed_3525_: u8 = 0;
    let mut v_res_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3107__boxed_3525_ = (crate::leanh::lean_unbox(v___y_3518_) as u8);
    v_res_3526_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v___y_3107__boxed_3525_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
    crate::leanh::lean_dec(v___y_3523_);
    crate::leanh::lean_dec_ref(v___y_3522_);
    crate::leanh::lean_dec(v___y_3521_);
    crate::leanh::lean_dec_ref(v___y_3520_);
    crate::leanh::lean_dec(v___y_3519_);
    return v_res_3526_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(
    mut v_fvarId_3527_: *mut crate::leanh::LeanObject,
    mut v_a_3528_: u8,
    mut v_a_3529_: *mut crate::leanh::LeanObject,
    mut v_a_3530_: *mut crate::leanh::LeanObject,
    mut v_a_3531_: *mut crate::leanh::LeanObject,
    mut v_a_3532_: *mut crate::leanh::LeanObject,
    mut v_a_3533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3535_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_);
                if crate::leanh::lean_obj_tag(v___x_3535_) == 0 {
                    v_a_3536_ = crate::leanh::lean_ctor_get(v___x_3535_, 0);
                    v_isSharedCheck_3547_ = (!crate::leanh::lean_is_exclusive(v___x_3535_)) as u8;
                    if v_isSharedCheck_3547_ == 0 {
                        v___x_3538_ = v___x_3535_;
                        v_isShared_3539_ = v_isSharedCheck_3547_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3536_);
                        crate::leanh::lean_dec(v___x_3535_);
                        v___x_3538_ = crate::leanh::lean_box(0);
                        v_isShared_3539_ = v_isSharedCheck_3547_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_3527_);
                    return v___x_3535_;
                }
            }
            1 => {
                v___x_3540_ = lean_st_ref_take(v_a_3529_);
                crate::leanh::lean_inc(v_a_3536_);
                v___x_3541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3541_, 0, v_a_3536_);
                v___x_3542_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v___x_3540_, v_fvarId_3527_, v___x_3541_);
                v___x_3543_ = lean_st_ref_set(v_a_3529_, v___x_3542_);
                if v_isShared_3539_ == 0 {
                    v___x_3545_ = v___x_3538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3546_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3536_);
                    v___x_3545_ = v_reuseFailAlloc_3546_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3545_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(
    mut v_fvarId_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_a_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3556_: u8 = 0;
    let mut v_res_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3556_ = (crate::leanh::lean_unbox(v_a_3549_) as u8);
    v_res_3557_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_3548_, v_a_boxed_3556_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_);
    crate::leanh::lean_dec(v_a_3554_);
    crate::leanh::lean_dec_ref(v_a_3553_);
    crate::leanh::lean_dec(v_a_3552_);
    crate::leanh::lean_dec_ref(v_a_3551_);
    crate::leanh::lean_dec(v_a_3550_);
    return v_res_3557_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(
    mut v_pu_3558_: u8,
    mut v_fvarId_3559_: *mut crate::leanh::LeanObject,
    mut v_a_3560_: u8,
    mut v_a_3561_: *mut crate::leanh::LeanObject,
    mut v_a_3562_: *mut crate::leanh::LeanObject,
    mut v_a_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3567_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
    return v___x_3567_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(
    mut v_pu_3568_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3569_: *mut crate::leanh::LeanObject,
    mut v_a_3570_: *mut crate::leanh::LeanObject,
    mut v_a_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
    mut v_a_3576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3577_: u8 = 0;
    let mut v_a_boxed_3578_: u8 = 0;
    let mut v_res_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3577_ = (crate::leanh::lean_unbox(v_pu_3568_) as u8);
    v_a_boxed_3578_ = (crate::leanh::lean_unbox(v_a_3570_) as u8);
    v_res_3579_ =
        l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(
            v_pu_boxed_3577_,
            v_fvarId_3569_,
            v_a_boxed_3578_,
            v_a_3571_,
            v_a_3572_,
            v_a_3573_,
            v_a_3574_,
            v_a_3575_,
        );
    crate::leanh::lean_dec(v_a_3575_);
    crate::leanh::lean_dec_ref(v_a_3574_);
    crate::leanh::lean_dec(v_a_3573_);
    crate::leanh::lean_dec_ref(v_a_3572_);
    crate::leanh::lean_dec(v_a_3571_);
    return v_res_3579_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(
    mut v___y_3580_: u8,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
    mut v___y_3583_: *mut crate::leanh::LeanObject,
    mut v___y_3584_: *mut crate::leanh::LeanObject,
    mut v___y_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3587_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(v___y_3585_);
    return v___x_3587_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(
    mut v___y_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
    mut v___y_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3182__boxed_3595_: u8 = 0;
    let mut v_res_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3182__boxed_3595_ = (crate::leanh::lean_unbox(v___y_3588_) as u8);
    v_res_3596_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(v___y_3182__boxed_3595_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
    crate::leanh::lean_dec(v___y_3593_);
    crate::leanh::lean_dec_ref(v___y_3592_);
    crate::leanh::lean_dec(v___y_3591_);
    crate::leanh::lean_dec_ref(v___y_3590_);
    crate::leanh::lean_dec(v___y_3589_);
    return v_res_3596_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(
    mut v_00_u03b2_3597_: *mut crate::leanh::LeanObject,
    mut v_m_3598_: *mut crate::leanh::LeanObject,
    mut v_a_3599_: *mut crate::leanh::LeanObject,
    mut v_b_3600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3601_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(v_m_3598_, v_a_3599_, v_b_3600_);
    return v___x_3601_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(
    mut v_00_u03b2_3602_: *mut crate::leanh::LeanObject,
    mut v_a_3603_: *mut crate::leanh::LeanObject,
    mut v_x_3604_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3605_: u8 = 0;
    v___x_3605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(v_a_3603_, v_x_3604_);
    return v___x_3605_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(
    mut v_00_u03b2_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
    mut v_x_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3609_: u8 = 0;
    let mut v_r_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3609_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(v_00_u03b2_3606_, v_a_3607_, v_x_3608_);
    crate::leanh::lean_dec(v_x_3608_);
    crate::leanh::lean_dec(v_a_3607_);
    v_r_3610_ = crate::leanh::lean_box((v_res_3609_) as usize);
    return v_r_3610_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(
    mut v_00_u03b2_3611_: *mut crate::leanh::LeanObject,
    mut v_data_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3613_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(v_data_3612_);
    return v___x_3613_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(
    mut v_00_u03b2_3614_: *mut crate::leanh::LeanObject,
    mut v_a_3615_: *mut crate::leanh::LeanObject,
    mut v_b_3616_: *mut crate::leanh::LeanObject,
    mut v_x_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3618_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(v_a_3615_, v_b_3616_, v_x_3617_);
    return v___x_3618_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(
    mut v_00_u03b2_3619_: *mut crate::leanh::LeanObject,
    mut v_i_3620_: *mut crate::leanh::LeanObject,
    mut v_source_3621_: *mut crate::leanh::LeanObject,
    mut v_target_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3623_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(v_i_3620_, v_source_3621_, v_target_3622_);
    return v___x_3623_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_3624_: *mut crate::leanh::LeanObject,
    mut v_x_3625_: *mut crate::leanh::LeanObject,
    mut v_x_3626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3627_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(v_x_3625_, v_x_3626_);
    return v___x_3627_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(
    mut v_a_3628_: *mut crate::leanh::LeanObject,
    mut v_x_3629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: u8 = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3629_) == 0 {
                    v___x_3630_ = crate::leanh::lean_box(0);
                    return v___x_3630_;
                } else {
                    v_key_3631_ = crate::leanh::lean_ctor_get(v_x_3629_, 0);
                    v_value_3632_ = crate::leanh::lean_ctor_get(v_x_3629_, 1);
                    v_tail_3633_ = crate::leanh::lean_ctor_get(v_x_3629_, 2);
                    v___x_3634_ = l_Lean_instBEqFVarId_beq(v_key_3631_, v_a_3628_);
                    if v___x_3634_ == 0 {
                        v_x_3629_ = v_tail_3633_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3632_);
                        v___x_3636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3636_, 0, v_value_3632_);
                        return v___x_3636_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(
    mut v_a_3637_: *mut crate::leanh::LeanObject,
    mut v_x_3638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3639_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_3637_, v_x_3638_);
    crate::leanh::lean_dec(v_x_3638_);
    crate::leanh::lean_dec(v_a_3637_);
    return v_res_3639_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(
    mut v_m_3640_: *mut crate::leanh::LeanObject,
    mut v_a_3641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u64 = 0;
    let mut v___x_3645_: u64 = 0;
    let mut v___x_3646_: u64 = 0;
    let mut v_fold_3647_: u64 = 0;
    let mut v___x_3648_: u64 = 0;
    let mut v___x_3649_: u64 = 0;
    let mut v___x_3650_: u64 = 0;
    let mut v___x_3651_: usize = 0;
    let mut v___x_3652_: usize = 0;
    let mut v___x_3653_: usize = 0;
    let mut v___x_3654_: usize = 0;
    let mut v___x_3655_: usize = 0;
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3642_ = crate::leanh::lean_ctor_get(v_m_3640_, 1);
    v___x_3643_ = lean_array_get_size(v_buckets_3642_);
    v___x_3644_ = l_Lean_instHashableFVarId_hash(v_a_3641_);
    v___x_3645_ = 32u64;
    v___x_3646_ = lean_uint64_shift_right(v___x_3644_, v___x_3645_);
    v_fold_3647_ = lean_uint64_xor(v___x_3644_, v___x_3646_);
    v___x_3648_ = 16u64;
    v___x_3649_ = lean_uint64_shift_right(v_fold_3647_, v___x_3648_);
    v___x_3650_ = lean_uint64_xor(v_fold_3647_, v___x_3649_);
    v___x_3651_ = lean_uint64_to_usize(v___x_3650_);
    v___x_3652_ = lean_usize_of_nat(v___x_3643_);
    v___x_3653_ = 1usize;
    v___x_3654_ = lean_usize_sub(v___x_3652_, v___x_3653_);
    v___x_3655_ = lean_usize_land(v___x_3651_, v___x_3654_);
    v___x_3656_ = lean_array_uget_borrowed(v_buckets_3642_, v___x_3655_);
    v___x_3657_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_3641_, v___x_3656_);
    return v___x_3657_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(
    mut v_m_3658_: *mut crate::leanh::LeanObject,
    mut v_a_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_3658_, v_a_3659_);
    crate::leanh::lean_dec(v_a_3659_);
    crate::leanh::lean_dec_ref(v_m_3658_);
    return v_res_3660_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3661_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3661_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(
    mut v_msg_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: u8,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3679_: u8 = 0;
    let mut v_toFunctor_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___f_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3703_: u8 = 0;
    let mut v_toFunctor_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v___f_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8158__overap_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3732_: u8 = 0;
    let mut v_unused_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3734_: u8 = 0;
    let mut v_unused_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3738_: u8 = 0;
    let mut v_unused_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3740_: u8 = 0;
    let mut v_unused_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3674_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
                v___x_3675_ = l_StateRefT_x27_instMonad___redArg(v___x_3674_);
                v_toApplicative_3676_ = crate::leanh::lean_ctor_get(v___x_3675_, 0);
                v_isSharedCheck_3740_ = (!crate::leanh::lean_is_exclusive(v___x_3675_)) as u8;
                if v_isSharedCheck_3740_ == 0 {
                    v_unused_3741_ = crate::leanh::lean_ctor_get(v___x_3675_, 1);
                    crate::leanh::lean_dec(v_unused_3741_);
                    v___x_3678_ = v___x_3675_;
                    v_isShared_3679_ = v_isSharedCheck_3740_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3676_);
                    crate::leanh::lean_dec(v___x_3675_);
                    v___x_3678_ = crate::leanh::lean_box(0);
                    v_isShared_3679_ = v_isSharedCheck_3740_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3680_ = crate::leanh::lean_ctor_get(v_toApplicative_3676_, 0);
                v_toSeq_3681_ = crate::leanh::lean_ctor_get(v_toApplicative_3676_, 2);
                v_toSeqLeft_3682_ = crate::leanh::lean_ctor_get(v_toApplicative_3676_, 3);
                v_toSeqRight_3683_ = crate::leanh::lean_ctor_get(v_toApplicative_3676_, 4);
                v_isSharedCheck_3738_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3676_)) as u8;
                if v_isSharedCheck_3738_ == 0 {
                    v_unused_3739_ = crate::leanh::lean_ctor_get(v_toApplicative_3676_, 1);
                    crate::leanh::lean_dec(v_unused_3739_);
                    v___x_3685_ = v_toApplicative_3676_;
                    v_isShared_3686_ = v_isSharedCheck_3738_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3683_);
                    crate::leanh::lean_inc(v_toSeqLeft_3682_);
                    crate::leanh::lean_inc(v_toSeq_3681_);
                    crate::leanh::lean_inc(v_toFunctor_3680_);
                    crate::leanh::lean_dec(v_toApplicative_3676_);
                    v___x_3685_ = crate::leanh::lean_box(0);
                    v_isShared_3686_ = v_isSharedCheck_3738_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3687_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1;
                v___f_3688_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_3680_);
                v___f_3689_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3689_, 0, v_toFunctor_3680_);
                v___f_3690_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3690_, 0, v_toFunctor_3680_);
                v___x_3691_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3691_, 0, v___f_3689_);
                crate::leanh::lean_ctor_set(v___x_3691_, 1, v___f_3690_);
                v___f_3692_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3692_, 0, v_toSeqRight_3683_);
                v___f_3693_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3693_, 0, v_toSeqLeft_3682_);
                v___f_3694_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3694_, 0, v_toSeq_3681_);
                if v_isShared_3686_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3685_, 4, v___f_3692_);
                    crate::leanh::lean_ctor_set(v___x_3685_, 3, v___f_3693_);
                    crate::leanh::lean_ctor_set(v___x_3685_, 2, v___f_3694_);
                    crate::leanh::lean_ctor_set(v___x_3685_, 1, v___f_3687_);
                    crate::leanh::lean_ctor_set(v___x_3685_, 0, v___x_3691_);
                    v___x_3696_ = v___x_3685_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 1, v___f_3687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 2, v___f_3694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 3, v___f_3693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 4, v___f_3692_);
                    v___x_3696_ = v_reuseFailAlloc_3737_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3679_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3678_, 1, v___f_3688_);
                    crate::leanh::lean_ctor_set(v___x_3678_, 0, v___x_3696_);
                    v___x_3698_ = v___x_3678_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 1, v___f_3688_);
                    v___x_3698_ = v_reuseFailAlloc_3736_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3699_ = l_StateRefT_x27_instMonad___redArg(v___x_3698_);
                v_toApplicative_3700_ = crate::leanh::lean_ctor_get(v___x_3699_, 0);
                v_isSharedCheck_3734_ = (!crate::leanh::lean_is_exclusive(v___x_3699_)) as u8;
                if v_isSharedCheck_3734_ == 0 {
                    v_unused_3735_ = crate::leanh::lean_ctor_get(v___x_3699_, 1);
                    crate::leanh::lean_dec(v_unused_3735_);
                    v___x_3702_ = v___x_3699_;
                    v_isShared_3703_ = v_isSharedCheck_3734_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3700_);
                    crate::leanh::lean_dec(v___x_3699_);
                    v___x_3702_ = crate::leanh::lean_box(0);
                    v_isShared_3703_ = v_isSharedCheck_3734_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3704_ = crate::leanh::lean_ctor_get(v_toApplicative_3700_, 0);
                v_toSeq_3705_ = crate::leanh::lean_ctor_get(v_toApplicative_3700_, 2);
                v_toSeqLeft_3706_ = crate::leanh::lean_ctor_get(v_toApplicative_3700_, 3);
                v_toSeqRight_3707_ = crate::leanh::lean_ctor_get(v_toApplicative_3700_, 4);
                v_isSharedCheck_3732_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3700_)) as u8;
                if v_isSharedCheck_3732_ == 0 {
                    v_unused_3733_ = crate::leanh::lean_ctor_get(v_toApplicative_3700_, 1);
                    crate::leanh::lean_dec(v_unused_3733_);
                    v___x_3709_ = v_toApplicative_3700_;
                    v_isShared_3710_ = v_isSharedCheck_3732_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3707_);
                    crate::leanh::lean_inc(v_toSeqLeft_3706_);
                    crate::leanh::lean_inc(v_toSeq_3705_);
                    crate::leanh::lean_inc(v_toFunctor_3704_);
                    crate::leanh::lean_dec(v_toApplicative_3700_);
                    v___x_3709_ = crate::leanh::lean_box(0);
                    v_isShared_3710_ = v_isSharedCheck_3732_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3711_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3;
                v___f_3712_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_3704_);
                v___f_3713_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3713_, 0, v_toFunctor_3704_);
                v___f_3714_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3714_, 0, v_toFunctor_3704_);
                v___x_3715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3715_, 0, v___f_3713_);
                crate::leanh::lean_ctor_set(v___x_3715_, 1, v___f_3714_);
                v___f_3716_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3716_, 0, v_toSeqRight_3707_);
                v___f_3717_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3717_, 0, v_toSeqLeft_3706_);
                v___f_3718_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3718_, 0, v_toSeq_3705_);
                if v_isShared_3710_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3709_, 4, v___f_3716_);
                    crate::leanh::lean_ctor_set(v___x_3709_, 3, v___f_3717_);
                    crate::leanh::lean_ctor_set(v___x_3709_, 2, v___f_3718_);
                    crate::leanh::lean_ctor_set(v___x_3709_, 1, v___f_3711_);
                    crate::leanh::lean_ctor_set(v___x_3709_, 0, v___x_3715_);
                    v___x_3720_ = v___x_3709_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3731_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 1, v___f_3711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 2, v___f_3718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 3, v___f_3717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 4, v___f_3716_);
                    v___x_3720_ = v_reuseFailAlloc_3731_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3702_, 1, v___f_3712_);
                    crate::leanh::lean_ctor_set(v___x_3702_, 0, v___x_3720_);
                    v___x_3722_ = v___x_3702_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3730_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3730_, 1, v___f_3712_);
                    v___x_3722_ = v_reuseFailAlloc_3730_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3723_ = l_StateRefT_x27_instMonad___redArg(v___x_3722_);
                v___x_3724_ = l_Lean_instInhabitedExpr;
                v___x_3725_ = l_instInhabitedOfMonad___redArg(v___x_3723_, v___x_3724_);
                v___f_3726_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3726_, 0, v___x_3725_);
                v___x_8158__overap_3727_ = lean_panic_fn_borrowed(v___f_3726_, v_msg_3666_);
                crate::leanh::lean_dec_ref(v___f_3726_);
                v___x_3728_ = crate::leanh::lean_box((v___y_3667_) as usize);
                crate::leanh::lean_inc(v___y_3672_);
                crate::leanh::lean_inc_ref(v___y_3671_);
                crate::leanh::lean_inc(v___y_3670_);
                crate::leanh::lean_inc_ref(v___y_3669_);
                crate::leanh::lean_inc(v___y_3668_);
                v___x_3729_ = crate::leanh::lean_apply_7(
                    v___x_8158__overap_3727_,
                    v___x_3728_,
                    v___y_3668_,
                    v___y_3669_,
                    v___y_3670_,
                    v___y_3671_,
                    v___y_3672_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(
    mut v_msg_3742_: *mut crate::leanh::LeanObject,
    mut v___y_3743_: *mut crate::leanh::LeanObject,
    mut v___y_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
    mut v___y_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_8278__boxed_3750_: u8 = 0;
    let mut v_res_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_8278__boxed_3750_ = (crate::leanh::lean_unbox(v___y_3743_) as u8);
    v_res_3751_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v_msg_3742_, v___y_8278__boxed_3750_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
    crate::leanh::lean_dec(v___y_3748_);
    crate::leanh::lean_dec_ref(v___y_3747_);
    crate::leanh::lean_dec(v___y_3746_);
    crate::leanh::lean_dec_ref(v___y_3745_);
    crate::leanh::lean_dec(v___y_3744_);
    return v_res_3751_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3755_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_3756_ = crate::leanh::lean_unsigned_to_nat(20);
    v___x_3757_ = crate::leanh::lean_unsigned_to_nat(88);
    v___x_3758_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1;
    v___x_3759_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_3760_ = l_mkPanicMessageWithDecl(
        v___x_3759_,
        v___x_3758_,
        v___x_3757_,
        v___x_3756_,
        v___x_3755_,
    );
    return v___x_3760_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(
    mut v_pu_3761_: u8,
    mut v_e_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: u8,
    mut v_a_3764_: *mut crate::leanh::LeanObject,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
    mut v_a_3766_: *mut crate::leanh::LeanObject,
    mut v_a_3767_: *mut crate::leanh::LeanObject,
    mut v_a_3768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3770_: u8 = 0;
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3779_: u8 = 0;
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v_unused_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3804_: u8 = 0;
    let mut v_a_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3812_: u8 = 0;
    let mut v_expr_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3816_: u8 = 0;
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3820_: u8 = 0;
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut v_fn_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v___y_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3838_: u8 = 0;
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: usize = 0;
    let mut v___x_3841_: usize = 0;
    let mut v___x_3842_: u8 = 0;
    let mut v___x_3843_: usize = 0;
    let mut v___x_3844_: usize = 0;
    let mut v___x_3845_: u8 = 0;
    let mut v_isSharedCheck_3846_: u8 = 0;
    let mut v_binderName_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3850_: u8 = 0;
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___y_3859_: u8 = 0;
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: usize = 0;
    let mut v___x_3873_: usize = 0;
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: usize = 0;
    let mut v___x_3876_: usize = 0;
    let mut v___x_3877_: u8 = 0;
    let mut v_isSharedCheck_3878_: u8 = 0;
    let mut v_binderName_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3882_: u8 = 0;
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3889_: u8 = 0;
    let mut v___y_3891_: u8 = 0;
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: u8 = 0;
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: usize = 0;
    let mut v___x_3905_: usize = 0;
    let mut v___x_3906_: u8 = 0;
    let mut v___x_3907_: usize = 0;
    let mut v___x_3908_: usize = 0;
    let mut v___x_3909_: u8 = 0;
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3919_: u8 = 0;
    let mut v___x_3920_: usize = 0;
    let mut v___x_3921_: usize = 0;
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut v_typeName_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3939_: usize = 0;
    let mut v___x_3940_: usize = 0;
    let mut v___x_3941_: u8 = 0;
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3770_ = l_Lean_Expr_hasFVar(v_e_3762_);
                if v___x_3770_ == 0 {
                    v___x_3771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3771_, 0, v_e_3762_);
                    return v___x_3771_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_3762_) {
                        1 => {
                            v_fvarId_3772_ = crate::leanh::lean_ctor_get(v_e_3762_, 0);
                            v___x_3773_ = lean_st_ref_get(v_a_3764_);
                            v___x_3774_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_3773_, v_fvarId_3772_);
                            crate::leanh::lean_dec(v___x_3773_);
                            if crate::leanh::lean_obj_tag(v___x_3774_) == 0 {
                                v___x_3775_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3775_, 0, v_e_3762_);
                                return v___x_3775_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_3762_, 1);
                                v_val_3776_ = crate::leanh::lean_ctor_get(v___x_3774_, 0);
                                v_isSharedCheck_3821_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3774_)) as u8;
                                if v_isSharedCheck_3821_ == 0 {
                                    v___x_3778_ = v___x_3774_;
                                    v_isShared_3779_ = v_isSharedCheck_3821_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3776_);
                                    crate::leanh::lean_dec(v___x_3774_);
                                    v___x_3778_ = crate::leanh::lean_box(0);
                                    v_isShared_3779_ = v_isSharedCheck_3821_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        5 => {
                            v_fn_3822_ = crate::leanh::lean_ctor_get(v_e_3762_, 0);
                            v_arg_3823_ = crate::leanh::lean_ctor_get(v_e_3762_, 1);
                            crate::leanh::lean_inc_ref(v_fn_3822_);
                            v___x_3824_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_3761_, v_fn_3822_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                            if crate::leanh::lean_obj_tag(v___x_3824_) == 0 {
                                v_a_3825_ = crate::leanh::lean_ctor_get(v___x_3824_, 0);
                                crate::leanh::lean_inc(v_a_3825_);
                                crate::leanh::lean_dec_ref_known(v___x_3824_, 1);
                                crate::leanh::lean_inc_ref(v_arg_3823_);
                                v___x_3826_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_3761_, v_arg_3823_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                                if crate::leanh::lean_obj_tag(v___x_3826_) == 0 {
                                    v_a_3827_ = crate::leanh::lean_ctor_get(v___x_3826_, 0);
                                    v_isSharedCheck_3846_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3826_)) as u8;
                                    if v_isSharedCheck_3846_ == 0 {
                                        v___x_3829_ = v___x_3826_;
                                        v_isShared_3830_ = v_isSharedCheck_3846_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3827_);
                                        crate::leanh::lean_dec(v___x_3826_);
                                        v___x_3829_ = crate::leanh::lean_box(0);
                                        v_isShared_3830_ = v_isSharedCheck_3846_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3825_);
                                    crate::leanh::lean_dec_ref_known(v_e_3762_, 2);
                                    return v___x_3826_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_3762_, 2);
                                return v___x_3824_;
                            }
                        }
                        6 => {
                            v_binderName_3847_ = crate::leanh::lean_ctor_get(v_e_3762_, 0);
                            v_binderType_3848_ = crate::leanh::lean_ctor_get(v_e_3762_, 1);
                            v_body_3849_ = crate::leanh::lean_ctor_get(v_e_3762_, 2);
                            v_binderInfo_3850_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_3762_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_3848_);
                            v___x_3851_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_3761_, v_binderType_3848_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                            if crate::leanh::lean_obj_tag(v___x_3851_) == 0 {
                                v_a_3852_ = crate::leanh::lean_ctor_get(v___x_3851_, 0);
                                crate::leanh::lean_inc(v_a_3852_);
                                crate::leanh::lean_dec_ref_known(v___x_3851_, 1);
                                crate::leanh::lean_inc_ref(v_body_3849_);
                                v___x_3853_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_3761_, v_body_3849_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                                if crate::leanh::lean_obj_tag(v___x_3853_) == 0 {
                                    v_a_3854_ = crate::leanh::lean_ctor_get(v___x_3853_, 0);
                                    v_isSharedCheck_3878_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3853_)) as u8;
                                    if v_isSharedCheck_3878_ == 0 {
                                        v___x_3856_ = v___x_3853_;
                                        v_isShared_3857_ = v_isSharedCheck_3878_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3854_);
                                        crate::leanh::lean_dec(v___x_3853_);
                                        v___x_3856_ = crate::leanh::lean_box(0);
                                        v_isShared_3857_ = v_isSharedCheck_3878_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3852_);
                                    crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                                    return v___x_3853_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                                return v___x_3851_;
                            }
                        }
                        7 => {
                            v_binderName_3879_ = crate::leanh::lean_ctor_get(v_e_3762_, 0);
                            v_binderType_3880_ = crate::leanh::lean_ctor_get(v_e_3762_, 1);
                            v_body_3881_ = crate::leanh::lean_ctor_get(v_e_3762_, 2);
                            v_binderInfo_3882_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_3762_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_3880_);
                            v___x_3883_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_3761_, v_binderType_3880_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                            if crate::leanh::lean_obj_tag(v___x_3883_) == 0 {
                                v_a_3884_ = crate::leanh::lean_ctor_get(v___x_3883_, 0);
                                crate::leanh::lean_inc(v_a_3884_);
                                crate::leanh::lean_dec_ref_known(v___x_3883_, 1);
                                crate::leanh::lean_inc_ref(v_body_3881_);
                                v___x_3885_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_3761_, v_body_3881_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                                if crate::leanh::lean_obj_tag(v___x_3885_) == 0 {
                                    v_a_3886_ = crate::leanh::lean_ctor_get(v___x_3885_, 0);
                                    v_isSharedCheck_3910_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3885_)) as u8;
                                    if v_isSharedCheck_3910_ == 0 {
                                        v___x_3888_ = v___x_3885_;
                                        v_isShared_3889_ = v_isSharedCheck_3910_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3886_);
                                        crate::leanh::lean_dec(v___x_3885_);
                                        v___x_3888_ = crate::leanh::lean_box(0);
                                        v_isShared_3889_ = v_isSharedCheck_3910_;
                                        state = 21;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3884_);
                                    crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                                    return v___x_3885_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                                return v___x_3883_;
                            }
                        }
                        8 => {
                            crate::leanh::lean_dec_ref_known(v_e_3762_, 4);
                            v___x_3911_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once), _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
                            v___x_3912_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(v___x_3911_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                            return v___x_3912_;
                        }
                        10 => {
                            v_data_3913_ = crate::leanh::lean_ctor_get(v_e_3762_, 0);
                            v_expr_3914_ = crate::leanh::lean_ctor_get(v_e_3762_, 1);
                            crate::leanh::lean_inc_ref(v_expr_3914_);
                            v___x_3915_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_3761_, v_expr_3914_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                            if crate::leanh::lean_obj_tag(v___x_3915_) == 0 {
                                v_a_3916_ = crate::leanh::lean_ctor_get(v___x_3915_, 0);
                                v_isSharedCheck_3930_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3915_)) as u8;
                                if v_isSharedCheck_3930_ == 0 {
                                    v___x_3918_ = v___x_3915_;
                                    v_isShared_3919_ = v_isSharedCheck_3930_;
                                    state = 26;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3916_);
                                    crate::leanh::lean_dec(v___x_3915_);
                                    v___x_3918_ = crate::leanh::lean_box(0);
                                    v_isShared_3919_ = v_isSharedCheck_3930_;
                                    state = 26;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_3762_, 2);
                                return v___x_3915_;
                            }
                        }
                        11 => {
                            v_typeName_3931_ = crate::leanh::lean_ctor_get(v_e_3762_, 0);
                            v_idx_3932_ = crate::leanh::lean_ctor_get(v_e_3762_, 1);
                            v_struct_3933_ = crate::leanh::lean_ctor_get(v_e_3762_, 2);
                            crate::leanh::lean_inc_ref(v_struct_3933_);
                            v___x_3934_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_3761_, v_struct_3933_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                            if crate::leanh::lean_obj_tag(v___x_3934_) == 0 {
                                v_a_3935_ = crate::leanh::lean_ctor_get(v___x_3934_, 0);
                                v_isSharedCheck_3949_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3934_)) as u8;
                                if v_isSharedCheck_3949_ == 0 {
                                    v___x_3937_ = v___x_3934_;
                                    v_isShared_3938_ = v_isSharedCheck_3949_;
                                    state = 29;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3935_);
                                    crate::leanh::lean_dec(v___x_3934_);
                                    v___x_3937_ = crate::leanh::lean_box(0);
                                    v_isShared_3938_ = v_isSharedCheck_3949_;
                                    state = 29;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                                return v___x_3934_;
                            }
                        }
                        _ => {
                            v___x_3950_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3950_, 0, v_e_3762_);
                            return v___x_3950_;
                        }
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_val_3776_) {
                0 => {
                    v___x_3780_ = l_Lean_Compiler_LCNF_erasedExpr;
                    if v_isShared_3779_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3778_, 0);
                        crate::leanh::lean_ctor_set(v___x_3778_, 0, v___x_3780_);
                        v___x_3782_ = v___x_3778_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
                        v___x_3782_ = v_reuseFailAlloc_3783_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_3778_);
                    v_fvarId_3784_ = crate::leanh::lean_ctor_get(v_val_3776_, 0);
                    crate::leanh::lean_inc(v_fvarId_3784_);
                    crate::leanh::lean_dec_ref_known(v_val_3776_, 1);
                    v___x_3785_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(
                        v_pu_3761_,
                        v_fvarId_3784_,
                        v_a_3766_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3785_) == 0 {
                        v_a_3786_ = crate::leanh::lean_ctor_get(v___x_3785_, 0);
                        v_isSharedCheck_3804_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3785_)) as u8;
                        if v_isSharedCheck_3804_ == 0 {
                            v___x_3788_ = v___x_3785_;
                            v_isShared_3789_ = v_isSharedCheck_3804_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3786_);
                            crate::leanh::lean_dec(v___x_3785_);
                            v___x_3788_ = crate::leanh::lean_box(0);
                            v_isShared_3789_ = v_isSharedCheck_3804_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_3784_);
                        v_a_3805_ = crate::leanh::lean_ctor_get(v___x_3785_, 0);
                        v_isSharedCheck_3812_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3785_)) as u8;
                        if v_isSharedCheck_3812_ == 0 {
                            v___x_3807_ = v___x_3785_;
                            v_isShared_3808_ = v_isSharedCheck_3812_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3805_);
                            crate::leanh::lean_dec(v___x_3785_);
                            v___x_3807_ = crate::leanh::lean_box(0);
                            v_isShared_3808_ = v_isSharedCheck_3812_;
                            state = 8;
                            continue;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_3778_);
                    v_expr_3813_ = crate::leanh::lean_ctor_get(v_val_3776_, 0);
                    v_isSharedCheck_3820_ = (!crate::leanh::lean_is_exclusive(v_val_3776_)) as u8;
                    if v_isSharedCheck_3820_ == 0 {
                        v___x_3815_ = v_val_3776_;
                        v_isShared_3816_ = v_isSharedCheck_3820_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_expr_3813_);
                        crate::leanh::lean_dec(v_val_3776_);
                        v___x_3815_ = crate::leanh::lean_box(0);
                        v_isShared_3816_ = v_isSharedCheck_3820_;
                        state = 10;
                        continue;
                    }
                }
            },
            2 => {
                return v___x_3782_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_3786_) == 0 {
                    crate::leanh::lean_dec(v_fvarId_3784_);
                    state = 4;
                    continue;
                } else {
                    v_isSharedCheck_3802_ = (!crate::leanh::lean_is_exclusive(v_a_3786_)) as u8;
                    if v_isSharedCheck_3802_ == 0 {
                        v_unused_3803_ = crate::leanh::lean_ctor_get(v_a_3786_, 0);
                        crate::leanh::lean_dec(v_unused_3803_);
                        v___x_3796_ = v_a_3786_;
                        v_isShared_3797_ = v_isSharedCheck_3802_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_3786_);
                        v___x_3796_ = crate::leanh::lean_box(0);
                        v_isShared_3797_ = v_isSharedCheck_3802_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3791_ = l_Lean_Compiler_LCNF_anyExpr;
                if v_isShared_3789_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3788_, 0, v___x_3791_);
                    v___x_3793_ = v___x_3788_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3791_);
                    v___x_3793_ = v_reuseFailAlloc_3794_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3793_;
            }
            6 => {
                if v___x_3770_ == 0 {
                    crate::leanh::lean_del_object(v___x_3796_);
                    crate::leanh::lean_dec(v_fvarId_3784_);
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_3788_);
                    v___x_3798_ = l_Lean_Expr_fvar___override(v_fvarId_3784_);
                    if v_isShared_3797_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3796_, 0);
                        crate::leanh::lean_ctor_set(v___x_3796_, 0, v___x_3798_);
                        v___x_3800_ = v___x_3796_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
                        v___x_3800_ = v_reuseFailAlloc_3801_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3800_;
            }
            8 => {
                if v_isShared_3808_ == 0 {
                    v___x_3810_ = v___x_3807_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
                    v___x_3810_ = v_reuseFailAlloc_3811_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3810_;
            }
            10 => {
                if v_isShared_3816_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3815_, 0);
                    v___x_3818_ = v___x_3815_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_expr_3813_);
                    v___x_3818_ = v_reuseFailAlloc_3819_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3818_;
            }
            12 => {
                v___x_3840_ = lean_ptr_addr(v_fn_3822_);
                v___x_3841_ = lean_ptr_addr(v_a_3825_);
                v___x_3842_ = lean_usize_dec_eq(v___x_3840_, v___x_3841_);
                if v___x_3842_ == 0 {
                    v___y_3838_ = v___x_3842_;
                    state = 15;
                    continue;
                } else {
                    v___x_3843_ = lean_ptr_addr(v_arg_3823_);
                    v___x_3844_ = lean_ptr_addr(v_a_3827_);
                    v___x_3845_ = lean_usize_dec_eq(v___x_3843_, v___x_3844_);
                    v___y_3838_ = v___x_3845_;
                    state = 15;
                    continue;
                }
            }
            13 => {
                v___x_3833_ = l_Lean_Expr_headBeta(v___y_3832_);
                if v_isShared_3830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3829_, 0, v___x_3833_);
                    v___x_3835_ = v___x_3829_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3836_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
                    v___x_3835_ = v_reuseFailAlloc_3836_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3835_;
            }
            15 => {
                if v___y_3838_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_3762_, 2);
                    v___x_3839_ = l_Lean_Expr_app___override(v_a_3825_, v_a_3827_);
                    v___y_3832_ = v___x_3839_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3827_);
                    crate::leanh::lean_dec(v_a_3825_);
                    v___y_3832_ = v_e_3762_;
                    state = 13;
                    continue;
                }
            }
            16 => {
                v___x_3872_ = lean_ptr_addr(v_binderType_3848_);
                v___x_3873_ = lean_ptr_addr(v_a_3852_);
                v___x_3874_ = lean_usize_dec_eq(v___x_3872_, v___x_3873_);
                if v___x_3874_ == 0 {
                    v___y_3859_ = v___x_3874_;
                    state = 17;
                    continue;
                } else {
                    v___x_3875_ = lean_ptr_addr(v_body_3849_);
                    v___x_3876_ = lean_ptr_addr(v_a_3854_);
                    v___x_3877_ = lean_usize_dec_eq(v___x_3875_, v___x_3876_);
                    v___y_3859_ = v___x_3877_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v___y_3859_ == 0 {
                    crate::leanh::lean_inc(v_binderName_3847_);
                    crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                    v___x_3860_ = l_Lean_Expr_lam___override(
                        v_binderName_3847_,
                        v_a_3852_,
                        v_a_3854_,
                        v_binderInfo_3850_,
                    );
                    if v_isShared_3857_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3856_, 0, v___x_3860_);
                        v___x_3862_ = v___x_3856_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3860_);
                        v___x_3862_ = v_reuseFailAlloc_3863_;
                        state = 18;
                        continue;
                    }
                } else {
                    v___x_3864_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_3850_, v_binderInfo_3850_);
                    if v___x_3864_ == 0 {
                        crate::leanh::lean_inc(v_binderName_3847_);
                        crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                        v___x_3865_ = l_Lean_Expr_lam___override(
                            v_binderName_3847_,
                            v_a_3852_,
                            v_a_3854_,
                            v_binderInfo_3850_,
                        );
                        if v_isShared_3857_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3856_, 0, v___x_3865_);
                            v___x_3867_ = v___x_3856_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_3868_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
                            v___x_3867_ = v_reuseFailAlloc_3868_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3854_);
                        crate::leanh::lean_dec(v_a_3852_);
                        if v_isShared_3857_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3856_, 0, v_e_3762_);
                            v___x_3870_ = v___x_3856_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_3871_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_e_3762_);
                            v___x_3870_ = v_reuseFailAlloc_3871_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            18 => {
                return v___x_3862_;
            }
            19 => {
                return v___x_3867_;
            }
            20 => {
                return v___x_3870_;
            }
            21 => {
                v___x_3904_ = lean_ptr_addr(v_binderType_3880_);
                v___x_3905_ = lean_ptr_addr(v_a_3884_);
                v___x_3906_ = lean_usize_dec_eq(v___x_3904_, v___x_3905_);
                if v___x_3906_ == 0 {
                    v___y_3891_ = v___x_3906_;
                    state = 22;
                    continue;
                } else {
                    v___x_3907_ = lean_ptr_addr(v_body_3881_);
                    v___x_3908_ = lean_ptr_addr(v_a_3886_);
                    v___x_3909_ = lean_usize_dec_eq(v___x_3907_, v___x_3908_);
                    v___y_3891_ = v___x_3909_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v___y_3891_ == 0 {
                    crate::leanh::lean_inc(v_binderName_3879_);
                    crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                    v___x_3892_ = l_Lean_Expr_forallE___override(
                        v_binderName_3879_,
                        v_a_3884_,
                        v_a_3886_,
                        v_binderInfo_3882_,
                    );
                    if v_isShared_3889_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3888_, 0, v___x_3892_);
                        v___x_3894_ = v___x_3888_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_3895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3892_);
                        v___x_3894_ = v_reuseFailAlloc_3895_;
                        state = 23;
                        continue;
                    }
                } else {
                    v___x_3896_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_3882_, v_binderInfo_3882_);
                    if v___x_3896_ == 0 {
                        crate::leanh::lean_inc(v_binderName_3879_);
                        crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                        v___x_3897_ = l_Lean_Expr_forallE___override(
                            v_binderName_3879_,
                            v_a_3884_,
                            v_a_3886_,
                            v_binderInfo_3882_,
                        );
                        if v_isShared_3889_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3888_, 0, v___x_3897_);
                            v___x_3899_ = v___x_3888_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_3900_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3897_);
                            v___x_3899_ = v_reuseFailAlloc_3900_;
                            state = 24;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3886_);
                        crate::leanh::lean_dec(v_a_3884_);
                        if v_isShared_3889_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3888_, 0, v_e_3762_);
                            v___x_3902_ = v___x_3888_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_3903_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_e_3762_);
                            v___x_3902_ = v_reuseFailAlloc_3903_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            23 => {
                return v___x_3894_;
            }
            24 => {
                return v___x_3899_;
            }
            25 => {
                return v___x_3902_;
            }
            26 => {
                v___x_3920_ = lean_ptr_addr(v_expr_3914_);
                v___x_3921_ = lean_ptr_addr(v_a_3916_);
                v___x_3922_ = lean_usize_dec_eq(v___x_3920_, v___x_3921_);
                if v___x_3922_ == 0 {
                    crate::leanh::lean_inc(v_data_3913_);
                    crate::leanh::lean_dec_ref_known(v_e_3762_, 2);
                    v___x_3923_ = l_Lean_Expr_mdata___override(v_data_3913_, v_a_3916_);
                    if v_isShared_3919_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3918_, 0, v___x_3923_);
                        v___x_3925_ = v___x_3918_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_3926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
                        v___x_3925_ = v_reuseFailAlloc_3926_;
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3916_);
                    if v_isShared_3919_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3918_, 0, v_e_3762_);
                        v___x_3928_ = v___x_3918_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_3929_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_e_3762_);
                        v___x_3928_ = v_reuseFailAlloc_3929_;
                        state = 28;
                        continue;
                    }
                }
            }
            27 => {
                return v___x_3925_;
            }
            28 => {
                return v___x_3928_;
            }
            29 => {
                v___x_3939_ = lean_ptr_addr(v_struct_3933_);
                v___x_3940_ = lean_ptr_addr(v_a_3935_);
                v___x_3941_ = lean_usize_dec_eq(v___x_3939_, v___x_3940_);
                if v___x_3941_ == 0 {
                    crate::leanh::lean_inc(v_idx_3932_);
                    crate::leanh::lean_inc(v_typeName_3931_);
                    crate::leanh::lean_dec_ref_known(v_e_3762_, 3);
                    v___x_3942_ =
                        l_Lean_Expr_proj___override(v_typeName_3931_, v_idx_3932_, v_a_3935_);
                    if v_isShared_3938_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3937_, 0, v___x_3942_);
                        v___x_3944_ = v___x_3937_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_3945_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
                        v___x_3944_ = v_reuseFailAlloc_3945_;
                        state = 30;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3935_);
                    if v_isShared_3938_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3937_, 0, v_e_3762_);
                        v___x_3947_ = v___x_3937_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_e_3762_);
                        v___x_3947_ = v_reuseFailAlloc_3948_;
                        state = 31;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_3944_;
            }
            31 => {
                return v___x_3947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(
    mut v_pu_3951_: u8,
    mut v_e_3952_: *mut crate::leanh::LeanObject,
    mut v_a_3953_: u8,
    mut v_a_3954_: *mut crate::leanh::LeanObject,
    mut v_a_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
    mut v_a_3957_: *mut crate::leanh::LeanObject,
    mut v_a_3958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___y_3970_: u8 = 0;
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: usize = 0;
    let mut v___x_3979_: usize = 0;
    let mut v___x_3980_: u8 = 0;
    let mut v___x_3981_: usize = 0;
    let mut v___x_3982_: usize = 0;
    let mut v___x_3983_: u8 = 0;
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_3952_) == 5 {
                    v_fn_3960_ = crate::leanh::lean_ctor_get(v_e_3952_, 0);
                    v_arg_3961_ = crate::leanh::lean_ctor_get(v_e_3952_, 1);
                    crate::leanh::lean_inc_ref(v_fn_3960_);
                    v___x_3962_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_3951_, v_fn_3960_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
                    if crate::leanh::lean_obj_tag(v___x_3962_) == 0 {
                        v_a_3963_ = crate::leanh::lean_ctor_get(v___x_3962_, 0);
                        crate::leanh::lean_inc(v_a_3963_);
                        crate::leanh::lean_dec_ref_known(v___x_3962_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3961_);
                        v___x_3964_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_3951_, v_arg_3961_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
                        if crate::leanh::lean_obj_tag(v___x_3964_) == 0 {
                            v_a_3965_ = crate::leanh::lean_ctor_get(v___x_3964_, 0);
                            v_isSharedCheck_3984_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3964_)) as u8;
                            if v_isSharedCheck_3984_ == 0 {
                                v___x_3967_ = v___x_3964_;
                                v_isShared_3968_ = v_isSharedCheck_3984_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3965_);
                                crate::leanh::lean_dec(v___x_3964_);
                                v___x_3967_ = crate::leanh::lean_box(0);
                                v_isShared_3968_ = v_isSharedCheck_3984_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3963_);
                            crate::leanh::lean_dec_ref_known(v_e_3952_, 2);
                            return v___x_3964_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_3952_, 2);
                        return v___x_3962_;
                    }
                } else {
                    v___x_3985_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_3951_, v_e_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
                    return v___x_3985_;
                }
            }
            1 => {
                v___x_3978_ = lean_ptr_addr(v_fn_3960_);
                v___x_3979_ = lean_ptr_addr(v_a_3963_);
                v___x_3980_ = lean_usize_dec_eq(v___x_3978_, v___x_3979_);
                if v___x_3980_ == 0 {
                    v___y_3970_ = v___x_3980_;
                    state = 2;
                    continue;
                } else {
                    v___x_3981_ = lean_ptr_addr(v_arg_3961_);
                    v___x_3982_ = lean_ptr_addr(v_a_3965_);
                    v___x_3983_ = lean_usize_dec_eq(v___x_3981_, v___x_3982_);
                    v___y_3970_ = v___x_3983_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_3970_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_3952_, 2);
                    v___x_3971_ = l_Lean_Expr_app___override(v_a_3963_, v_a_3965_);
                    if v_isShared_3968_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3967_, 0, v___x_3971_);
                        v___x_3973_ = v___x_3967_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3974_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
                        v___x_3973_ = v_reuseFailAlloc_3974_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3965_);
                    crate::leanh::lean_dec(v_a_3963_);
                    if v_isShared_3968_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3967_, 0, v_e_3952_);
                        v___x_3976_ = v___x_3967_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_e_3952_);
                        v___x_3976_ = v_reuseFailAlloc_3977_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3973_;
            }
            4 => {
                return v___x_3976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(
    mut v_pu_3986_: *mut crate::leanh::LeanObject,
    mut v_e_3987_: *mut crate::leanh::LeanObject,
    mut v_a_3988_: *mut crate::leanh::LeanObject,
    mut v_a_3989_: *mut crate::leanh::LeanObject,
    mut v_a_3990_: *mut crate::leanh::LeanObject,
    mut v_a_3991_: *mut crate::leanh::LeanObject,
    mut v_a_3992_: *mut crate::leanh::LeanObject,
    mut v_a_3993_: *mut crate::leanh::LeanObject,
    mut v_a_3994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3995_: u8 = 0;
    let mut v_a_boxed_3996_: u8 = 0;
    let mut v_res_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3995_ = (crate::leanh::lean_unbox(v_pu_3986_) as u8);
    v_a_boxed_3996_ = (crate::leanh::lean_unbox(v_a_3988_) as u8);
    v_res_3997_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(v_pu_boxed_3995_, v_e_3987_, v_a_boxed_3996_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
    crate::leanh::lean_dec(v_a_3993_);
    crate::leanh::lean_dec_ref(v_a_3992_);
    crate::leanh::lean_dec(v_a_3991_);
    crate::leanh::lean_dec_ref(v_a_3990_);
    crate::leanh::lean_dec(v_a_3989_);
    return v_res_3997_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(
    mut v_pu_3998_: *mut crate::leanh::LeanObject,
    mut v_e_3999_: *mut crate::leanh::LeanObject,
    mut v_a_4000_: *mut crate::leanh::LeanObject,
    mut v_a_4001_: *mut crate::leanh::LeanObject,
    mut v_a_4002_: *mut crate::leanh::LeanObject,
    mut v_a_4003_: *mut crate::leanh::LeanObject,
    mut v_a_4004_: *mut crate::leanh::LeanObject,
    mut v_a_4005_: *mut crate::leanh::LeanObject,
    mut v_a_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4007_: u8 = 0;
    let mut v_a_boxed_4008_: u8 = 0;
    let mut v_res_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4007_ = (crate::leanh::lean_unbox(v_pu_3998_) as u8);
    v_a_boxed_4008_ = (crate::leanh::lean_unbox(v_a_4000_) as u8);
    v_res_4009_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_boxed_4007_, v_e_3999_, v_a_boxed_4008_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_);
    crate::leanh::lean_dec(v_a_4005_);
    crate::leanh::lean_dec_ref(v_a_4004_);
    crate::leanh::lean_dec(v_a_4003_);
    crate::leanh::lean_dec_ref(v_a_4002_);
    crate::leanh::lean_dec(v_a_4001_);
    return v_res_4009_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(
    mut v_00_u03b2_4010_: *mut crate::leanh::LeanObject,
    mut v_m_4011_: *mut crate::leanh::LeanObject,
    mut v_a_4012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v_m_4011_, v_a_4012_);
    return v___x_4013_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(
    mut v_00_u03b2_4014_: *mut crate::leanh::LeanObject,
    mut v_m_4015_: *mut crate::leanh::LeanObject,
    mut v_a_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4017_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(v_00_u03b2_4014_, v_m_4015_, v_a_4016_);
    crate::leanh::lean_dec(v_a_4016_);
    crate::leanh::lean_dec_ref(v_m_4015_);
    return v_res_4017_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(
    mut v_00_u03b2_4018_: *mut crate::leanh::LeanObject,
    mut v_a_4019_: *mut crate::leanh::LeanObject,
    mut v_x_4020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4021_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(v_a_4019_, v_x_4020_);
    return v___x_4021_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(
    mut v_00_u03b2_4022_: *mut crate::leanh::LeanObject,
    mut v_a_4023_: *mut crate::leanh::LeanObject,
    mut v_x_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4025_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(v_00_u03b2_4022_, v_a_4023_, v_x_4024_);
    crate::leanh::lean_dec(v_x_4024_);
    crate::leanh::lean_dec(v_a_4023_);
    return v_res_4025_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(
    mut v_pu_4026_: u8,
    mut v_e_4027_: *mut crate::leanh::LeanObject,
    mut v_a_4028_: u8,
    mut v_a_4029_: *mut crate::leanh::LeanObject,
    mut v_a_4030_: *mut crate::leanh::LeanObject,
    mut v_a_4031_: *mut crate::leanh::LeanObject,
    mut v_a_4032_: *mut crate::leanh::LeanObject,
    mut v_a_4033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: u8 = 0;
    v___x_4035_ = 1;
    v___x_4036_ = l_Lean_Compiler_LCNF_instDecidableEqPurity(v_pu_4026_, v___x_4035_);
    if v___x_4036_ == 0 {
        let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4037_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(v_pu_4026_, v_e_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_);
        return v___x_4037_;
    } else {
        let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4038_, 0, v_e_4027_);
        return v___x_4038_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(
    mut v_pu_4039_: *mut crate::leanh::LeanObject,
    mut v_e_4040_: *mut crate::leanh::LeanObject,
    mut v_a_4041_: *mut crate::leanh::LeanObject,
    mut v_a_4042_: *mut crate::leanh::LeanObject,
    mut v_a_4043_: *mut crate::leanh::LeanObject,
    mut v_a_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_a_4046_: *mut crate::leanh::LeanObject,
    mut v_a_4047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4048_: u8 = 0;
    let mut v_a_boxed_4049_: u8 = 0;
    let mut v_res_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4048_ = (crate::leanh::lean_unbox(v_pu_4039_) as u8);
    v_a_boxed_4049_ = (crate::leanh::lean_unbox(v_a_4041_) as u8);
    v_res_4050_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_boxed_4048_, v_e_4040_, v_a_boxed_4049_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
    crate::leanh::lean_dec(v_a_4046_);
    crate::leanh::lean_dec_ref(v_a_4045_);
    crate::leanh::lean_dec(v_a_4044_);
    crate::leanh::lean_dec_ref(v_a_4043_);
    crate::leanh::lean_dec(v_a_4042_);
    return v_res_4050_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeParam(
    mut v_pu_4051_: u8,
    mut v_p_4052_: *mut crate::leanh::LeanObject,
    mut v_a_4053_: u8,
    mut v_a_4054_: *mut crate::leanh::LeanObject,
    mut v_a_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
    mut v_a_4057_: *mut crate::leanh::LeanObject,
    mut v_a_4058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_4063_: u8 = 0;
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4066_: u8 = 0;
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4075_: u8 = 0;
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut v_isSharedCheck_4094_: u8 = 0;
    let mut v_a_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4098_: u8 = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4102_: u8 = 0;
    let mut v_a_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4060_ = crate::leanh::lean_ctor_get(v_p_4052_, 0);
                v_binderName_4061_ = crate::leanh::lean_ctor_get(v_p_4052_, 1);
                v_type_4062_ = crate::leanh::lean_ctor_get(v_p_4052_, 2);
                v_borrow_4063_ = crate::leanh::lean_ctor_get_uint8(
                    v_p_4052_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_4111_ = (!crate::leanh::lean_is_exclusive(v_p_4052_)) as u8;
                if v_isSharedCheck_4111_ == 0 {
                    v___x_4065_ = v_p_4052_;
                    v_isShared_4066_ = v_isSharedCheck_4111_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_type_4062_);
                    crate::leanh::lean_inc(v_binderName_4061_);
                    crate::leanh::lean_inc(v_fvarId_4060_);
                    crate::leanh::lean_dec(v_p_4052_);
                    v___x_4065_ = crate::leanh::lean_box(0);
                    v_isShared_4066_ = v_isSharedCheck_4111_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4067_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_4061_, v_a_4053_, v_a_4056_);
                v_a_4068_ = crate::leanh::lean_ctor_get(v___x_4067_, 0);
                crate::leanh::lean_inc(v_a_4068_);
                crate::leanh::lean_dec_ref(v___x_4067_);
                v___x_4069_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_4051_, v_type_4062_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
                if crate::leanh::lean_obj_tag(v___x_4069_) == 0 {
                    v_a_4070_ = crate::leanh::lean_ctor_get(v___x_4069_, 0);
                    crate::leanh::lean_inc(v_a_4070_);
                    crate::leanh::lean_dec_ref_known(v___x_4069_, 1);
                    v___x_4071_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_4060_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
                    if crate::leanh::lean_obj_tag(v___x_4071_) == 0 {
                        v_a_4072_ = crate::leanh::lean_ctor_get(v___x_4071_, 0);
                        v_isSharedCheck_4094_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4071_)) as u8;
                        if v_isSharedCheck_4094_ == 0 {
                            v___x_4074_ = v___x_4071_;
                            v_isShared_4075_ = v_isSharedCheck_4094_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4072_);
                            crate::leanh::lean_dec(v___x_4071_);
                            v___x_4074_ = crate::leanh::lean_box(0);
                            v_isShared_4075_ = v_isSharedCheck_4094_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4070_);
                        crate::leanh::lean_dec(v_a_4068_);
                        crate::leanh::lean_del_object(v___x_4065_);
                        v_a_4095_ = crate::leanh::lean_ctor_get(v___x_4071_, 0);
                        v_isSharedCheck_4102_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4071_)) as u8;
                        if v_isSharedCheck_4102_ == 0 {
                            v___x_4097_ = v___x_4071_;
                            v_isShared_4098_ = v_isSharedCheck_4102_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4095_);
                            crate::leanh::lean_dec(v___x_4071_);
                            v___x_4097_ = crate::leanh::lean_box(0);
                            v_isShared_4098_ = v_isSharedCheck_4102_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4068_);
                    crate::leanh::lean_del_object(v___x_4065_);
                    crate::leanh::lean_dec(v_fvarId_4060_);
                    v_a_4103_ = crate::leanh::lean_ctor_get(v___x_4069_, 0);
                    v_isSharedCheck_4110_ = (!crate::leanh::lean_is_exclusive(v___x_4069_)) as u8;
                    if v_isSharedCheck_4110_ == 0 {
                        v___x_4105_ = v___x_4069_;
                        v_isShared_4106_ = v_isSharedCheck_4110_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4103_);
                        crate::leanh::lean_dec(v___x_4069_);
                        v___x_4105_ = crate::leanh::lean_box(0);
                        v_isShared_4106_ = v_isSharedCheck_4110_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4076_ = lean_st_ref_take(v_a_4056_);
                v_lctx_4077_ = crate::leanh::lean_ctor_get(v___x_4076_, 0);
                v_nextIdx_4078_ = crate::leanh::lean_ctor_get(v___x_4076_, 1);
                v_isSharedCheck_4093_ = (!crate::leanh::lean_is_exclusive(v___x_4076_)) as u8;
                if v_isSharedCheck_4093_ == 0 {
                    v___x_4080_ = v___x_4076_;
                    v_isShared_4081_ = v_isSharedCheck_4093_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_4078_);
                    crate::leanh::lean_inc(v_lctx_4077_);
                    crate::leanh::lean_dec(v___x_4076_);
                    v___x_4080_ = crate::leanh::lean_box(0);
                    v_isShared_4081_ = v_isSharedCheck_4093_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4065_, 2, v_a_4070_);
                    crate::leanh::lean_ctor_set(v___x_4065_, 1, v_a_4068_);
                    crate::leanh::lean_ctor_set(v___x_4065_, 0, v_a_4072_);
                    v___x_4083_ = v___x_4065_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4092_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_a_4068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_a_4070_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4092_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_borrow_4063_,
                    );
                    v___x_4083_ = v_reuseFailAlloc_4092_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_4083_);
                v___x_4084_ =
                    l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_4051_, v_lctx_4077_, v___x_4083_);
                if v_isShared_4081_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4080_, 0, v___x_4084_);
                    v___x_4086_ = v___x_4080_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_nextIdx_4078_);
                    v___x_4086_ = v_reuseFailAlloc_4091_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4087_ = lean_st_ref_set(v_a_4056_, v___x_4086_);
                if v_isShared_4075_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4074_, 0, v___x_4083_);
                    v___x_4089_ = v___x_4074_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4090_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4083_);
                    v___x_4089_ = v_reuseFailAlloc_4090_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4089_;
            }
            7 => {
                if v_isShared_4098_ == 0 {
                    v___x_4100_ = v___x_4097_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
                    v___x_4100_ = v_reuseFailAlloc_4101_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4100_;
            }
            9 => {
                if v_isShared_4106_ == 0 {
                    v___x_4108_ = v___x_4105_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
                    v___x_4108_ = v_reuseFailAlloc_4109_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(
    mut v_pu_4112_: *mut crate::leanh::LeanObject,
    mut v_p_4113_: *mut crate::leanh::LeanObject,
    mut v_a_4114_: *mut crate::leanh::LeanObject,
    mut v_a_4115_: *mut crate::leanh::LeanObject,
    mut v_a_4116_: *mut crate::leanh::LeanObject,
    mut v_a_4117_: *mut crate::leanh::LeanObject,
    mut v_a_4118_: *mut crate::leanh::LeanObject,
    mut v_a_4119_: *mut crate::leanh::LeanObject,
    mut v_a_4120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4121_: u8 = 0;
    let mut v_a_boxed_4122_: u8 = 0;
    let mut v_res_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4121_ = (crate::leanh::lean_unbox(v_pu_4112_) as u8);
    v_a_boxed_4122_ = (crate::leanh::lean_unbox(v_a_4114_) as u8);
    v_res_4123_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(
        v_pu_boxed_4121_,
        v_p_4113_,
        v_a_boxed_4122_,
        v_a_4115_,
        v_a_4116_,
        v_a_4117_,
        v_a_4118_,
        v_a_4119_,
    );
    crate::leanh::lean_dec(v_a_4119_);
    crate::leanh::lean_dec_ref(v_a_4118_);
    crate::leanh::lean_dec(v_a_4117_);
    crate::leanh::lean_dec_ref(v_a_4116_);
    crate::leanh::lean_dec(v_a_4115_);
    return v_res_4123_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeArg(
    mut v_pu_4124_: u8,
    mut v_arg_4125_: *mut crate::leanh::LeanObject,
    mut v_a_4126_: u8,
    mut v_a_4127_: *mut crate::leanh::LeanObject,
    mut v_a_4128_: *mut crate::leanh::LeanObject,
    mut v_a_4129_: *mut crate::leanh::LeanObject,
    mut v_a_4130_: *mut crate::leanh::LeanObject,
    mut v_a_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4141_: u8 = 0;
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4149_: u8 = 0;
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_expr_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4167_: u8 = 0;
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v_expr_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4174_: u8 = 0;
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4179_: u8 = 0;
    let mut v_a_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4183_: u8 = 0;
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_arg_4125_) {
                0 => {
                    v___x_4133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4133_, 0, v_arg_4125_);
                    return v___x_4133_;
                }
                1 => {
                    v_fvarId_4134_ = crate::leanh::lean_ctor_get(v_arg_4125_, 0);
                    v___x_4135_ = lean_st_ref_get(v_a_4127_);
                    v___x_4136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(v___x_4135_, v_fvarId_4134_);
                    crate::leanh::lean_dec(v___x_4135_);
                    if crate::leanh::lean_obj_tag(v___x_4136_) == 0 {
                        v___x_4137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4137_, 0, v_arg_4125_);
                        return v___x_4137_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_arg_4125_, 1);
                        v_val_4138_ = crate::leanh::lean_ctor_get(v___x_4136_, 0);
                        v_isSharedCheck_4168_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4136_)) as u8;
                        if v_isSharedCheck_4168_ == 0 {
                            v___x_4140_ = v___x_4136_;
                            v_isShared_4141_ = v_isSharedCheck_4168_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4138_);
                            crate::leanh::lean_dec(v___x_4136_);
                            v___x_4140_ = crate::leanh::lean_box(0);
                            v_isShared_4141_ = v_isSharedCheck_4168_;
                            state = 1;
                            continue;
                        }
                    }
                }
                _ => {
                    v_expr_4169_ = crate::leanh::lean_ctor_get(v_arg_4125_, 0);
                    crate::leanh::lean_inc_ref(v_expr_4169_);
                    v___x_4170_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_4124_, v_expr_4169_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_);
                    if crate::leanh::lean_obj_tag(v___x_4170_) == 0 {
                        v_a_4171_ = crate::leanh::lean_ctor_get(v___x_4170_, 0);
                        v_isSharedCheck_4179_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4170_)) as u8;
                        if v_isSharedCheck_4179_ == 0 {
                            v___x_4173_ = v___x_4170_;
                            v_isShared_4174_ = v_isSharedCheck_4179_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4171_);
                            crate::leanh::lean_dec(v___x_4170_);
                            v___x_4173_ = crate::leanh::lean_box(0);
                            v_isShared_4174_ = v_isSharedCheck_4179_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_arg_4125_, 1);
                        v_a_4180_ = crate::leanh::lean_ctor_get(v___x_4170_, 0);
                        v_isSharedCheck_4187_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4170_)) as u8;
                        if v_isSharedCheck_4187_ == 0 {
                            v___x_4182_ = v___x_4170_;
                            v_isShared_4183_ = v_isSharedCheck_4187_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4180_);
                            crate::leanh::lean_dec(v___x_4170_);
                            v___x_4182_ = crate::leanh::lean_box(0);
                            v_isShared_4183_ = v_isSharedCheck_4187_;
                            state = 11;
                            continue;
                        }
                    }
                }
            },
            1 => match crate::leanh::lean_obj_tag(v_val_4138_) {
                0 => {
                    v___x_4142_ = crate::leanh::lean_box(0);
                    if v_isShared_4141_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4140_, 0);
                        crate::leanh::lean_ctor_set(v___x_4140_, 0, v___x_4142_);
                        v___x_4144_ = v___x_4140_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4142_);
                        v___x_4144_ = v_reuseFailAlloc_4145_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_fvarId_4146_ = crate::leanh::lean_ctor_get(v_val_4138_, 0);
                    v_isSharedCheck_4156_ = (!crate::leanh::lean_is_exclusive(v_val_4138_)) as u8;
                    if v_isSharedCheck_4156_ == 0 {
                        v___x_4148_ = v_val_4138_;
                        v_isShared_4149_ = v_isSharedCheck_4156_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_4146_);
                        crate::leanh::lean_dec(v_val_4138_);
                        v___x_4148_ = crate::leanh::lean_box(0);
                        v_isShared_4149_ = v_isSharedCheck_4156_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_expr_4157_ = crate::leanh::lean_ctor_get(v_val_4138_, 0);
                    v_isSharedCheck_4167_ = (!crate::leanh::lean_is_exclusive(v_val_4138_)) as u8;
                    if v_isSharedCheck_4167_ == 0 {
                        v___x_4159_ = v_val_4138_;
                        v_isShared_4160_ = v_isSharedCheck_4167_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_expr_4157_);
                        crate::leanh::lean_dec(v_val_4138_);
                        v___x_4159_ = crate::leanh::lean_box(0);
                        v_isShared_4160_ = v_isSharedCheck_4167_;
                        state = 6;
                        continue;
                    }
                }
            },
            2 => {
                return v___x_4144_;
            }
            3 => {
                if v_isShared_4149_ == 0 {
                    v___x_4151_ = v___x_4148_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_fvarId_4146_);
                    v___x_4151_ = v_reuseFailAlloc_4155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4141_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4140_, 0);
                    crate::leanh::lean_ctor_set(v___x_4140_, 0, v___x_4151_);
                    v___x_4153_ = v___x_4140_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4154_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4151_);
                    v___x_4153_ = v_reuseFailAlloc_4154_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4153_;
            }
            6 => {
                if v_isShared_4160_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4166_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_expr_4157_);
                    v___x_4162_ = v_reuseFailAlloc_4166_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4141_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4140_, 0);
                    crate::leanh::lean_ctor_set(v___x_4140_, 0, v___x_4162_);
                    v___x_4164_ = v___x_4140_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
                    v___x_4164_ = v_reuseFailAlloc_4165_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4164_;
            }
            9 => {
                v___x_4175_ =
                    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(
                        v_pu_4124_,
                        v_arg_4125_,
                        v_a_4171_,
                    );
                if v_isShared_4174_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4173_, 0, v___x_4175_);
                    v___x_4177_ = v___x_4173_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4175_);
                    v___x_4177_ = v_reuseFailAlloc_4178_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4177_;
            }
            11 => {
                if v_isShared_4183_ == 0 {
                    v___x_4185_ = v___x_4182_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
                    v___x_4185_ = v_reuseFailAlloc_4186_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(
    mut v_pu_4188_: *mut crate::leanh::LeanObject,
    mut v_arg_4189_: *mut crate::leanh::LeanObject,
    mut v_a_4190_: *mut crate::leanh::LeanObject,
    mut v_a_4191_: *mut crate::leanh::LeanObject,
    mut v_a_4192_: *mut crate::leanh::LeanObject,
    mut v_a_4193_: *mut crate::leanh::LeanObject,
    mut v_a_4194_: *mut crate::leanh::LeanObject,
    mut v_a_4195_: *mut crate::leanh::LeanObject,
    mut v_a_4196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4197_: u8 = 0;
    let mut v_a_boxed_4198_: u8 = 0;
    let mut v_res_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4197_ = (crate::leanh::lean_unbox(v_pu_4188_) as u8);
    v_a_boxed_4198_ = (crate::leanh::lean_unbox(v_a_4190_) as u8);
    v_res_4199_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(
        v_pu_boxed_4197_,
        v_arg_4189_,
        v_a_boxed_4198_,
        v_a_4191_,
        v_a_4192_,
        v_a_4193_,
        v_a_4194_,
        v_a_4195_,
    );
    crate::leanh::lean_dec(v_a_4195_);
    crate::leanh::lean_dec_ref(v_a_4194_);
    crate::leanh::lean_dec(v_a_4193_);
    crate::leanh::lean_dec_ref(v_a_4192_);
    crate::leanh::lean_dec(v_a_4191_);
    return v_res_4199_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(
    mut v_pu_4200_: u8,
    mut v_sz_4201_: usize,
    mut v_i_4202_: usize,
    mut v_bs_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: u8,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
    mut v___y_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4211_: u8 = 0;
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: usize = 0;
    let mut v___x_4219_: usize = 0;
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4225_: u8 = 0;
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4211_ = lean_usize_dec_lt(v_i_4202_, v_sz_4201_);
                if v___x_4211_ == 0 {
                    v___x_4212_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4212_, 0, v_bs_4203_);
                    return v___x_4212_;
                } else {
                    v_v_4213_ = lean_array_uget_borrowed(v_bs_4203_, v_i_4202_);
                    crate::leanh::lean_inc(v_v_4213_);
                    v___x_4214_ = l_Lean_Compiler_LCNF_Internalize_internalizeArg(
                        v_pu_4200_,
                        v_v_4213_,
                        v___y_4204_,
                        v___y_4205_,
                        v___y_4206_,
                        v___y_4207_,
                        v___y_4208_,
                        v___y_4209_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4214_) == 0 {
                        v_a_4215_ = crate::leanh::lean_ctor_get(v___x_4214_, 0);
                        crate::leanh::lean_inc(v_a_4215_);
                        crate::leanh::lean_dec_ref_known(v___x_4214_, 1);
                        v___x_4216_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4217_ = lean_array_uset(v_bs_4203_, v_i_4202_, v___x_4216_);
                        v___x_4218_ = 1usize;
                        v___x_4219_ = lean_usize_add(v_i_4202_, v___x_4218_);
                        v___x_4220_ = lean_array_uset(v_bs_x27_4217_, v_i_4202_, v_a_4215_);
                        v_i_4202_ = v___x_4219_;
                        v_bs_4203_ = v___x_4220_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_4203_);
                        v_a_4222_ = crate::leanh::lean_ctor_get(v___x_4214_, 0);
                        v_isSharedCheck_4229_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4214_)) as u8;
                        if v_isSharedCheck_4229_ == 0 {
                            v___x_4224_ = v___x_4214_;
                            v_isShared_4225_ = v_isSharedCheck_4229_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4222_);
                            crate::leanh::lean_dec(v___x_4214_);
                            v___x_4224_ = crate::leanh::lean_box(0);
                            v_isShared_4225_ = v_isSharedCheck_4229_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4225_ == 0 {
                    v___x_4227_ = v___x_4224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
                    v___x_4227_ = v_reuseFailAlloc_4228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(
    mut v_pu_4230_: *mut crate::leanh::LeanObject,
    mut v_sz_4231_: *mut crate::leanh::LeanObject,
    mut v_i_4232_: *mut crate::leanh::LeanObject,
    mut v_bs_4233_: *mut crate::leanh::LeanObject,
    mut v___y_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4241_: u8 = 0;
    let mut v_sz_boxed_4242_: usize = 0;
    let mut v_i_boxed_4243_: usize = 0;
    let mut v___y_341__boxed_4244_: u8 = 0;
    let mut v_res_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4241_ = (crate::leanh::lean_unbox(v_pu_4230_) as u8);
    v_sz_boxed_4242_ = crate::leanh::lean_unbox_usize(v_sz_4231_);
    crate::leanh::lean_dec(v_sz_4231_);
    v_i_boxed_4243_ = crate::leanh::lean_unbox_usize(v_i_4232_);
    crate::leanh::lean_dec(v_i_4232_);
    v___y_341__boxed_4244_ = (crate::leanh::lean_unbox(v___y_4234_) as u8);
    v_res_4245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_boxed_4241_, v_sz_boxed_4242_, v_i_boxed_4243_, v_bs_4233_, v___y_341__boxed_4244_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
    crate::leanh::lean_dec(v___y_4239_);
    crate::leanh::lean_dec_ref(v___y_4238_);
    crate::leanh::lean_dec(v___y_4237_);
    crate::leanh::lean_dec_ref(v___y_4236_);
    crate::leanh::lean_dec(v___y_4235_);
    return v_res_4245_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeArgs(
    mut v_pu_4246_: u8,
    mut v_args_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: u8,
    mut v_a_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
    mut v_a_4253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4255_: usize = 0;
    let mut v___x_4256_: usize = 0;
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4255_ = lean_array_size(v_args_4247_);
    v___x_4256_ = 0usize;
    v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(v_pu_4246_, v_sz_4255_, v___x_4256_, v_args_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_);
    return v___x_4257_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(
    mut v_pu_4258_: *mut crate::leanh::LeanObject,
    mut v_args_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4267_: u8 = 0;
    let mut v_a_boxed_4268_: u8 = 0;
    let mut v_res_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4267_ = (crate::leanh::lean_unbox(v_pu_4258_) as u8);
    v_a_boxed_4268_ = (crate::leanh::lean_unbox(v_a_4260_) as u8);
    v_res_4269_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(
        v_pu_boxed_4267_,
        v_args_4259_,
        v_a_boxed_4268_,
        v_a_4261_,
        v_a_4262_,
        v_a_4263_,
        v_a_4264_,
        v_a_4265_,
    );
    crate::leanh::lean_dec(v_a_4265_);
    crate::leanh::lean_dec_ref(v_a_4264_);
    crate::leanh::lean_dec(v_a_4263_);
    crate::leanh::lean_dec_ref(v_a_4262_);
    crate::leanh::lean_dec(v_a_4261_);
    return v_res_4269_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(
    mut v_pu_4270_: u8,
    mut v_e_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: u8,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
    mut v_a_4274_: *mut crate::leanh::LeanObject,
    mut v_a_4275_: *mut crate::leanh::LeanObject,
    mut v_a_4276_: *mut crate::leanh::LeanObject,
    mut v_a_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: u8 = 0;
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4293_: u8 = 0;
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: u8 = 0;
    let mut v___y_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4308_: u8 = 0;
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4313_: u8 = 0;
    let mut v_a_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4317_: u8 = 0;
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4321_: u8 = 0;
    let mut v_struct_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4329_: u8 = 0;
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4334_: u8 = 0;
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut v_a_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4351_: u8 = 0;
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut v_fvarId_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut v_a_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4375_: u8 = 0;
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut v_a_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4396_: u8 = 0;
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4400_: u8 = 0;
    let mut v_var_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: u8 = 0;
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4415_: u8 = 0;
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: u8 = 0;
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4428_: u8 = 0;
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4433_: u8 = 0;
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_4438_: u8 = 0;
    let mut v_args_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: u8 = 0;
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4448_: u8 = 0;
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4453_: u8 = 0;
    let mut v_a_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4457_: u8 = 0;
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4461_: u8 = 0;
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: u8 = 0;
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4472_: u8 = 0;
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: u8 = 0;
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4487_: u8 = 0;
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4492_: u8 = 0;
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4495_: u8 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut v_unused_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: u8 = 0;
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v_unused_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_4271_) {
                2 => {
                    v_struct_4322_ = crate::leanh::lean_ctor_get(v_e_4271_, 2);
                    v___x_4323_ = lean_st_ref_get(v_a_4273_);
                    v___x_4324_ = 1;
                    crate::leanh::lean_inc(v_struct_4322_);
                    v___x_4325_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_4323_,
                        v_struct_4322_,
                        v___x_4324_,
                    );
                    crate::leanh::lean_dec(v___x_4323_);
                    if crate::leanh::lean_obj_tag(v___x_4325_) == 0 {
                        v_fvarId_4326_ = crate::leanh::lean_ctor_get(v___x_4325_, 0);
                        v_isSharedCheck_4334_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4325_)) as u8;
                        if v_isSharedCheck_4334_ == 0 {
                            v___x_4328_ = v___x_4325_;
                            v_isShared_4329_ = v_isSharedCheck_4334_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_4326_);
                            crate::leanh::lean_dec(v___x_4325_);
                            v___x_4328_ = crate::leanh::lean_box(0);
                            v_isShared_4329_ = v_isSharedCheck_4334_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_4271_, 3);
                        v___x_4335_ = crate::leanh::lean_box(1);
                        v___x_4336_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4336_, 0, v___x_4335_);
                        return v___x_4336_;
                    }
                }
                3 => {
                    v_args_4337_ = crate::leanh::lean_ctor_get(v_e_4271_, 2);
                    crate::leanh::lean_inc_ref(v_args_4337_);
                    v___x_4338_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(
                        v_pu_4270_,
                        v_args_4337_,
                        v_a_4272_,
                        v_a_4273_,
                        v_a_4274_,
                        v_a_4275_,
                        v_a_4276_,
                        v_a_4277_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4338_) == 0 {
                        v_a_4339_ = crate::leanh::lean_ctor_get(v___x_4338_, 0);
                        v_isSharedCheck_4347_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4338_)) as u8;
                        if v_isSharedCheck_4347_ == 0 {
                            v___x_4341_ = v___x_4338_;
                            v_isShared_4342_ = v_isSharedCheck_4347_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4339_);
                            crate::leanh::lean_dec(v___x_4338_);
                            v___x_4341_ = crate::leanh::lean_box(0);
                            v_isShared_4342_ = v_isSharedCheck_4347_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_4271_, 3);
                        v_a_4348_ = crate::leanh::lean_ctor_get(v___x_4338_, 0);
                        v_isSharedCheck_4355_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4338_)) as u8;
                        if v_isSharedCheck_4355_ == 0 {
                            v___x_4350_ = v___x_4338_;
                            v_isShared_4351_ = v_isSharedCheck_4355_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4348_);
                            crate::leanh::lean_dec(v___x_4338_);
                            v___x_4350_ = crate::leanh::lean_box(0);
                            v_isShared_4351_ = v_isSharedCheck_4355_;
                            state = 13;
                            continue;
                        }
                    }
                }
                4 => {
                    v_fvarId_4356_ = crate::leanh::lean_ctor_get(v_e_4271_, 0);
                    v_args_4357_ = crate::leanh::lean_ctor_get(v_e_4271_, 1);
                    v___x_4358_ = lean_st_ref_get(v_a_4273_);
                    v___x_4359_ = 1;
                    crate::leanh::lean_inc(v_fvarId_4356_);
                    v___x_4360_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_4358_,
                        v_fvarId_4356_,
                        v___x_4359_,
                    );
                    crate::leanh::lean_dec(v___x_4358_);
                    if crate::leanh::lean_obj_tag(v___x_4360_) == 0 {
                        v_fvarId_4361_ = crate::leanh::lean_ctor_get(v___x_4360_, 0);
                        crate::leanh::lean_inc(v_fvarId_4361_);
                        crate::leanh::lean_dec_ref_known(v___x_4360_, 1);
                        crate::leanh::lean_inc_ref(v_args_4357_);
                        v___x_4362_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(
                            v_pu_4270_,
                            v_args_4357_,
                            v_a_4272_,
                            v_a_4273_,
                            v_a_4274_,
                            v_a_4275_,
                            v_a_4276_,
                            v_a_4277_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4362_) == 0 {
                            v_a_4363_ = crate::leanh::lean_ctor_get(v___x_4362_, 0);
                            v_isSharedCheck_4371_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4362_)) as u8;
                            if v_isSharedCheck_4371_ == 0 {
                                v___x_4365_ = v___x_4362_;
                                v_isShared_4366_ = v_isSharedCheck_4371_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4363_);
                                crate::leanh::lean_dec(v___x_4362_);
                                v___x_4365_ = crate::leanh::lean_box(0);
                                v_isShared_4366_ = v_isSharedCheck_4371_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_4361_);
                            crate::leanh::lean_dec_ref_known(v_e_4271_, 2);
                            v_a_4372_ = crate::leanh::lean_ctor_get(v___x_4362_, 0);
                            v_isSharedCheck_4379_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4362_)) as u8;
                            if v_isSharedCheck_4379_ == 0 {
                                v___x_4374_ = v___x_4362_;
                                v_isShared_4375_ = v_isSharedCheck_4379_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4372_);
                                crate::leanh::lean_dec(v___x_4362_);
                                v___x_4374_ = crate::leanh::lean_box(0);
                                v_isShared_4375_ = v_isSharedCheck_4379_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_4271_, 2);
                        v___x_4380_ = crate::leanh::lean_box(1);
                        v___x_4381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4381_, 0, v___x_4380_);
                        return v___x_4381_;
                    }
                }
                5 => {
                    v_args_4382_ = crate::leanh::lean_ctor_get(v_e_4271_, 1);
                    crate::leanh::lean_inc_ref(v_args_4382_);
                    v___x_4383_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(
                        v_pu_4270_,
                        v_args_4382_,
                        v_a_4272_,
                        v_a_4273_,
                        v_a_4274_,
                        v_a_4275_,
                        v_a_4276_,
                        v_a_4277_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4383_) == 0 {
                        v_a_4384_ = crate::leanh::lean_ctor_get(v___x_4383_, 0);
                        v_isSharedCheck_4392_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4383_)) as u8;
                        if v_isSharedCheck_4392_ == 0 {
                            v___x_4386_ = v___x_4383_;
                            v_isShared_4387_ = v_isSharedCheck_4392_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4384_);
                            crate::leanh::lean_dec(v___x_4383_);
                            v___x_4386_ = crate::leanh::lean_box(0);
                            v_isShared_4387_ = v_isSharedCheck_4392_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_4271_, 2);
                        v_a_4393_ = crate::leanh::lean_ctor_get(v___x_4383_, 0);
                        v_isSharedCheck_4400_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4383_)) as u8;
                        if v_isSharedCheck_4400_ == 0 {
                            v___x_4395_ = v___x_4383_;
                            v_isShared_4396_ = v_isSharedCheck_4400_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4393_);
                            crate::leanh::lean_dec(v___x_4383_);
                            v___x_4395_ = crate::leanh::lean_box(0);
                            v_isShared_4396_ = v_isSharedCheck_4400_;
                            state = 21;
                            continue;
                        }
                    }
                }
                6 => {
                    v_var_4401_ = crate::leanh::lean_ctor_get(v_e_4271_, 1);
                    crate::leanh::lean_inc(v_var_4401_);
                    v_fvarId_4280_ = v_var_4401_;
                    v___y_4281_ = v_a_4273_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_var_4402_ = crate::leanh::lean_ctor_get(v_e_4271_, 1);
                    crate::leanh::lean_inc(v_var_4402_);
                    v_fvarId_4280_ = v_var_4402_;
                    v___y_4281_ = v_a_4273_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_var_4403_ = crate::leanh::lean_ctor_get(v_e_4271_, 2);
                    v___x_4404_ = lean_st_ref_get(v_a_4273_);
                    v___x_4405_ = 1;
                    crate::leanh::lean_inc(v_var_4403_);
                    v___x_4406_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_4404_,
                        v_var_4403_,
                        v___x_4405_,
                    );
                    crate::leanh::lean_dec(v___x_4404_);
                    if crate::leanh::lean_obj_tag(v___x_4406_) == 0 {
                        v_fvarId_4407_ = crate::leanh::lean_ctor_get(v___x_4406_, 0);
                        v_isSharedCheck_4415_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4406_)) as u8;
                        if v_isSharedCheck_4415_ == 0 {
                            v___x_4409_ = v___x_4406_;
                            v_isShared_4410_ = v_isSharedCheck_4415_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_4407_);
                            crate::leanh::lean_dec(v___x_4406_);
                            v___x_4409_ = crate::leanh::lean_box(0);
                            v_isShared_4410_ = v_isSharedCheck_4415_;
                            state = 23;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_4271_, 3);
                        v___x_4416_ = crate::leanh::lean_box(1);
                        v___x_4417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4417_, 0, v___x_4416_);
                        return v___x_4417_;
                    }
                }
                9 => {
                    v_args_4418_ = crate::leanh::lean_ctor_get(v_e_4271_, 1);
                    crate::leanh::lean_inc_ref(v_args_4418_);
                    v_args_4297_ = v_args_4418_;
                    v___y_4298_ = v_a_4272_;
                    v___y_4299_ = v_a_4273_;
                    v___y_4300_ = v_a_4274_;
                    v___y_4301_ = v_a_4275_;
                    v___y_4302_ = v_a_4276_;
                    v___y_4303_ = v_a_4277_;
                    state = 4;
                    continue;
                }
                10 => {
                    v_args_4419_ = crate::leanh::lean_ctor_get(v_e_4271_, 1);
                    crate::leanh::lean_inc_ref(v_args_4419_);
                    v_args_4297_ = v_args_4419_;
                    v___y_4298_ = v_a_4272_;
                    v___y_4299_ = v_a_4273_;
                    v___y_4300_ = v_a_4274_;
                    v___y_4301_ = v_a_4275_;
                    v___y_4302_ = v_a_4276_;
                    v___y_4303_ = v_a_4277_;
                    state = 4;
                    continue;
                }
                11 => {
                    v_n_4420_ = crate::leanh::lean_ctor_get(v_e_4271_, 0);
                    crate::leanh::lean_inc(v_n_4420_);
                    v_var_4421_ = crate::leanh::lean_ctor_get(v_e_4271_, 1);
                    v___x_4422_ = lean_st_ref_get(v_a_4273_);
                    v___x_4423_ = 1;
                    crate::leanh::lean_inc(v_var_4421_);
                    v___x_4424_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_4422_,
                        v_var_4421_,
                        v___x_4423_,
                    );
                    crate::leanh::lean_dec(v___x_4422_);
                    if crate::leanh::lean_obj_tag(v___x_4424_) == 0 {
                        v_fvarId_4425_ = crate::leanh::lean_ctor_get(v___x_4424_, 0);
                        v_isSharedCheck_4433_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4424_)) as u8;
                        if v_isSharedCheck_4433_ == 0 {
                            v___x_4427_ = v___x_4424_;
                            v_isShared_4428_ = v_isSharedCheck_4433_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_4425_);
                            crate::leanh::lean_dec(v___x_4424_);
                            v___x_4427_ = crate::leanh::lean_box(0);
                            v_isShared_4428_ = v_isSharedCheck_4433_;
                            state = 25;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_n_4420_);
                        crate::leanh::lean_dec_ref_known(v_e_4271_, 2);
                        v___x_4434_ = crate::leanh::lean_box(1);
                        v___x_4435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4435_, 0, v___x_4434_);
                        return v___x_4435_;
                    }
                }
                12 => {
                    v_var_4436_ = crate::leanh::lean_ctor_get(v_e_4271_, 0);
                    v_i_4437_ = crate::leanh::lean_ctor_get(v_e_4271_, 1);
                    crate::leanh::lean_inc_ref(v_i_4437_);
                    v_updateHeader_4438_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_4271_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_args_4439_ = crate::leanh::lean_ctor_get(v_e_4271_, 2);
                    v___x_4440_ = lean_st_ref_get(v_a_4273_);
                    v___x_4441_ = 1;
                    crate::leanh::lean_inc(v_var_4436_);
                    v___x_4442_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_4440_,
                        v_var_4436_,
                        v___x_4441_,
                    );
                    crate::leanh::lean_dec(v___x_4440_);
                    if crate::leanh::lean_obj_tag(v___x_4442_) == 0 {
                        v_fvarId_4443_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
                        crate::leanh::lean_inc(v_fvarId_4443_);
                        crate::leanh::lean_dec_ref_known(v___x_4442_, 1);
                        crate::leanh::lean_inc_ref(v_args_4439_);
                        v___x_4444_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(
                            v_pu_4270_,
                            v_args_4439_,
                            v_a_4272_,
                            v_a_4273_,
                            v_a_4274_,
                            v_a_4275_,
                            v_a_4276_,
                            v_a_4277_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4444_) == 0 {
                            v_a_4445_ = crate::leanh::lean_ctor_get(v___x_4444_, 0);
                            v_isSharedCheck_4453_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4444_)) as u8;
                            if v_isSharedCheck_4453_ == 0 {
                                v___x_4447_ = v___x_4444_;
                                v_isShared_4448_ = v_isSharedCheck_4453_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4445_);
                                crate::leanh::lean_dec(v___x_4444_);
                                v___x_4447_ = crate::leanh::lean_box(0);
                                v_isShared_4448_ = v_isSharedCheck_4453_;
                                state = 27;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_4443_);
                            crate::leanh::lean_dec_ref(v_i_4437_);
                            crate::leanh::lean_dec_ref_known(v_e_4271_, 3);
                            v_a_4454_ = crate::leanh::lean_ctor_get(v___x_4444_, 0);
                            v_isSharedCheck_4461_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4444_)) as u8;
                            if v_isSharedCheck_4461_ == 0 {
                                v___x_4456_ = v___x_4444_;
                                v_isShared_4457_ = v_isSharedCheck_4461_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4454_);
                                crate::leanh::lean_dec(v___x_4444_);
                                v___x_4456_ = crate::leanh::lean_box(0);
                                v_isShared_4457_ = v_isSharedCheck_4461_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_i_4437_);
                        crate::leanh::lean_dec_ref_known(v_e_4271_, 3);
                        v___x_4462_ = crate::leanh::lean_box(1);
                        v___x_4463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4463_, 0, v___x_4462_);
                        return v___x_4463_;
                    }
                }
                13 => {
                    v_ty_4464_ = crate::leanh::lean_ctor_get(v_e_4271_, 0);
                    crate::leanh::lean_inc_ref(v_ty_4464_);
                    v_fvarId_4465_ = crate::leanh::lean_ctor_get(v_e_4271_, 1);
                    v___x_4466_ = lean_st_ref_get(v_a_4273_);
                    v___x_4467_ = 1;
                    crate::leanh::lean_inc(v_fvarId_4465_);
                    v___x_4468_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_4466_,
                        v_fvarId_4465_,
                        v___x_4467_,
                    );
                    crate::leanh::lean_dec(v___x_4466_);
                    if crate::leanh::lean_obj_tag(v___x_4468_) == 0 {
                        v_fvarId_4469_ = crate::leanh::lean_ctor_get(v___x_4468_, 0);
                        v_isSharedCheck_4477_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4468_)) as u8;
                        if v_isSharedCheck_4477_ == 0 {
                            v___x_4471_ = v___x_4468_;
                            v_isShared_4472_ = v_isSharedCheck_4477_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_4469_);
                            crate::leanh::lean_dec(v___x_4468_);
                            v___x_4471_ = crate::leanh::lean_box(0);
                            v_isShared_4472_ = v_isSharedCheck_4477_;
                            state = 31;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_4271_, 2);
                        crate::leanh::lean_dec_ref(v_ty_4464_);
                        v___x_4478_ = crate::leanh::lean_box(1);
                        v___x_4479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4479_, 0, v___x_4478_);
                        return v___x_4479_;
                    }
                }
                14 => {
                    v_fvarId_4480_ = crate::leanh::lean_ctor_get(v_e_4271_, 0);
                    v___x_4481_ = lean_st_ref_get(v_a_4273_);
                    v___x_4482_ = 1;
                    crate::leanh::lean_inc(v_fvarId_4480_);
                    v___x_4483_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_4481_,
                        v_fvarId_4480_,
                        v___x_4482_,
                    );
                    crate::leanh::lean_dec(v___x_4481_);
                    if crate::leanh::lean_obj_tag(v___x_4483_) == 0 {
                        v_fvarId_4484_ = crate::leanh::lean_ctor_get(v___x_4483_, 0);
                        v_isSharedCheck_4492_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4483_)) as u8;
                        if v_isSharedCheck_4492_ == 0 {
                            v___x_4486_ = v___x_4483_;
                            v_isShared_4487_ = v_isSharedCheck_4492_;
                            state = 33;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_4484_);
                            crate::leanh::lean_dec(v___x_4483_);
                            v___x_4486_ = crate::leanh::lean_box(0);
                            v_isShared_4487_ = v_isSharedCheck_4492_;
                            state = 33;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_4500_ = (!crate::leanh::lean_is_exclusive(v_e_4271_)) as u8;
                        if v_isSharedCheck_4500_ == 0 {
                            v_unused_4501_ = crate::leanh::lean_ctor_get(v_e_4271_, 0);
                            crate::leanh::lean_dec(v_unused_4501_);
                            v___x_4494_ = v_e_4271_;
                            v_isShared_4495_ = v_isSharedCheck_4500_;
                            state = 35;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_e_4271_);
                            v___x_4494_ = crate::leanh::lean_box(0);
                            v_isShared_4495_ = v_isSharedCheck_4500_;
                            state = 35;
                            continue;
                        }
                    }
                }
                15 => {
                    v_fvarId_4502_ = crate::leanh::lean_ctor_get(v_e_4271_, 0);
                    v___x_4503_ = lean_st_ref_get(v_a_4273_);
                    v___x_4504_ = 1;
                    crate::leanh::lean_inc(v_fvarId_4502_);
                    v___x_4505_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_4503_,
                        v_fvarId_4502_,
                        v___x_4504_,
                    );
                    crate::leanh::lean_dec(v___x_4503_);
                    if crate::leanh::lean_obj_tag(v___x_4505_) == 0 {
                        v_fvarId_4506_ = crate::leanh::lean_ctor_get(v___x_4505_, 0);
                        v_isSharedCheck_4514_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4505_)) as u8;
                        if v_isSharedCheck_4514_ == 0 {
                            v___x_4508_ = v___x_4505_;
                            v_isShared_4509_ = v_isSharedCheck_4514_;
                            state = 37;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_4506_);
                            crate::leanh::lean_dec(v___x_4505_);
                            v___x_4508_ = crate::leanh::lean_box(0);
                            v_isShared_4509_ = v_isSharedCheck_4514_;
                            state = 37;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_4522_ = (!crate::leanh::lean_is_exclusive(v_e_4271_)) as u8;
                        if v_isSharedCheck_4522_ == 0 {
                            v_unused_4523_ = crate::leanh::lean_ctor_get(v_e_4271_, 0);
                            crate::leanh::lean_dec(v_unused_4523_);
                            v___x_4516_ = v_e_4271_;
                            v_isShared_4517_ = v_isSharedCheck_4522_;
                            state = 39;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_e_4271_);
                            v___x_4516_ = crate::leanh::lean_box(0);
                            v_isShared_4517_ = v_isSharedCheck_4522_;
                            state = 39;
                            continue;
                        }
                    }
                }
                _ => {
                    v___x_4524_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4524_, 0, v_e_4271_);
                    return v___x_4524_;
                }
            },
            1 => {
                v___x_4282_ = lean_st_ref_get(v___y_4281_);
                v___x_4283_ = 1;
                v___x_4284_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_4282_,
                    v_fvarId_4280_,
                    v___x_4283_,
                );
                crate::leanh::lean_dec(v___x_4282_);
                if crate::leanh::lean_obj_tag(v___x_4284_) == 0 {
                    v_fvarId_4285_ = crate::leanh::lean_ctor_get(v___x_4284_, 0);
                    v_isSharedCheck_4293_ = (!crate::leanh::lean_is_exclusive(v___x_4284_)) as u8;
                    if v_isSharedCheck_4293_ == 0 {
                        v___x_4287_ = v___x_4284_;
                        v_isShared_4288_ = v_isSharedCheck_4293_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_4285_);
                        crate::leanh::lean_dec(v___x_4284_);
                        v___x_4287_ = crate::leanh::lean_box(0);
                        v_isShared_4288_ = v_isSharedCheck_4293_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_e_4271_);
                    v___x_4294_ = crate::leanh::lean_box(1);
                    v___x_4295_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4295_, 0, v___x_4294_);
                    return v___x_4295_;
                }
            }
            2 => {
                v___x_4289_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_4270_, v_e_4271_, v_fvarId_4285_);
                if v_isShared_4288_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4287_, 0, v___x_4289_);
                    v___x_4291_ = v___x_4287_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4292_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4292_, 0, v___x_4289_);
                    v___x_4291_ = v_reuseFailAlloc_4292_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4291_;
            }
            4 => {
                v___x_4304_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(
                    v_pu_4270_,
                    v_args_4297_,
                    v___y_4298_,
                    v___y_4299_,
                    v___y_4300_,
                    v___y_4301_,
                    v___y_4302_,
                    v___y_4303_,
                );
                if crate::leanh::lean_obj_tag(v___x_4304_) == 0 {
                    v_a_4305_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                    v_isSharedCheck_4313_ = (!crate::leanh::lean_is_exclusive(v___x_4304_)) as u8;
                    if v_isSharedCheck_4313_ == 0 {
                        v___x_4307_ = v___x_4304_;
                        v_isShared_4308_ = v_isSharedCheck_4313_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4305_);
                        crate::leanh::lean_dec(v___x_4304_);
                        v___x_4307_ = crate::leanh::lean_box(0);
                        v_isShared_4308_ = v_isSharedCheck_4313_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_e_4271_);
                    v_a_4314_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                    v_isSharedCheck_4321_ = (!crate::leanh::lean_is_exclusive(v___x_4304_)) as u8;
                    if v_isSharedCheck_4321_ == 0 {
                        v___x_4316_ = v___x_4304_;
                        v_isShared_4317_ = v_isSharedCheck_4321_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4314_);
                        crate::leanh::lean_dec(v___x_4304_);
                        v___x_4316_ = crate::leanh::lean_box(0);
                        v_isShared_4317_ = v_isSharedCheck_4321_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4309_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_4270_, v_e_4271_, v_a_4305_);
                if v_isShared_4308_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4307_, 0, v___x_4309_);
                    v___x_4311_ = v___x_4307_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4309_);
                    v___x_4311_ = v_reuseFailAlloc_4312_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4311_;
            }
            7 => {
                if v_isShared_4317_ == 0 {
                    v___x_4319_ = v___x_4316_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
                    v___x_4319_ = v_reuseFailAlloc_4320_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4319_;
            }
            9 => {
                v___x_4330_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_4270_, v_e_4271_, v_fvarId_4326_);
                if v_isShared_4329_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4328_, 0, v___x_4330_);
                    v___x_4332_ = v___x_4328_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4333_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4330_);
                    v___x_4332_ = v_reuseFailAlloc_4333_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4332_;
            }
            11 => {
                v___x_4343_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_4270_, v_e_4271_, v_a_4339_);
                if v_isShared_4342_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4341_, 0, v___x_4343_);
                    v___x_4345_ = v___x_4341_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4343_);
                    v___x_4345_ = v_reuseFailAlloc_4346_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4345_;
            }
            13 => {
                if v_isShared_4351_ == 0 {
                    v___x_4353_ = v___x_4350_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4353_;
            }
            15 => {
                v___x_4367_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_4270_, v_e_4271_, v_fvarId_4361_, v_a_4363_);
                crate::leanh::lean_dec_ref_known(v_e_4271_, 2);
                if v_isShared_4366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4365_, 0, v___x_4367_);
                    v___x_4369_ = v___x_4365_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
                    v___x_4369_ = v_reuseFailAlloc_4370_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4369_;
            }
            17 => {
                if v_isShared_4375_ == 0 {
                    v___x_4377_ = v___x_4374_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
                    v___x_4377_ = v_reuseFailAlloc_4378_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4377_;
            }
            19 => {
                v___x_4388_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_4270_, v_e_4271_, v_a_4384_);
                if v_isShared_4387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4386_, 0, v___x_4388_);
                    v___x_4390_ = v___x_4386_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4391_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4388_);
                    v___x_4390_ = v_reuseFailAlloc_4391_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4390_;
            }
            21 => {
                if v_isShared_4396_ == 0 {
                    v___x_4398_ = v___x_4395_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4399_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
                    v___x_4398_ = v_reuseFailAlloc_4399_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4398_;
            }
            23 => {
                v___x_4411_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_4270_, v_e_4271_, v_fvarId_4407_);
                if v_isShared_4410_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4409_, 0, v___x_4411_);
                    v___x_4413_ = v___x_4409_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4414_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4411_);
                    v___x_4413_ = v_reuseFailAlloc_4414_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4413_;
            }
            25 => {
                v___x_4429_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_4270_, v_e_4271_, v_n_4420_, v_fvarId_4425_);
                crate::leanh::lean_dec_ref_known(v_e_4271_, 2);
                if v_isShared_4428_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4427_, 0, v___x_4429_);
                    v___x_4431_ = v___x_4427_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
                    v___x_4431_ = v_reuseFailAlloc_4432_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4431_;
            }
            27 => {
                v___x_4449_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_4270_, v_e_4271_, v_fvarId_4443_, v_i_4437_, v_updateHeader_4438_, v_a_4445_);
                if v_isShared_4448_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4447_, 0, v___x_4449_);
                    v___x_4451_ = v___x_4447_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4449_);
                    v___x_4451_ = v_reuseFailAlloc_4452_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4451_;
            }
            29 => {
                if v_isShared_4457_ == 0 {
                    v___x_4459_ = v___x_4456_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
                    v___x_4459_ = v_reuseFailAlloc_4460_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4459_;
            }
            31 => {
                v___x_4473_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_4270_, v_e_4271_, v_ty_4464_, v_fvarId_4469_);
                crate::leanh::lean_dec_ref_known(v_e_4271_, 2);
                if v_isShared_4472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4471_, 0, v___x_4473_);
                    v___x_4475_ = v___x_4471_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4476_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4473_);
                    v___x_4475_ = v_reuseFailAlloc_4476_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4475_;
            }
            33 => {
                v___x_4488_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_4270_, v_e_4271_, v_fvarId_4484_);
                if v_isShared_4487_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4486_, 0, v___x_4488_);
                    v___x_4490_ = v___x_4486_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4488_);
                    v___x_4490_ = v_reuseFailAlloc_4491_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4490_;
            }
            35 => {
                v___x_4496_ = crate::leanh::lean_box(1);
                if v_isShared_4495_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4494_, 0);
                    crate::leanh::lean_ctor_set(v___x_4494_, 0, v___x_4496_);
                    v___x_4498_ = v___x_4494_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
                    v___x_4498_ = v_reuseFailAlloc_4499_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4498_;
            }
            37 => {
                v___x_4510_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_4270_, v_e_4271_, v_fvarId_4506_);
                if v_isShared_4509_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4508_, 0, v___x_4510_);
                    v___x_4512_ = v___x_4508_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
                    v___x_4512_ = v_reuseFailAlloc_4513_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4512_;
            }
            39 => {
                v___x_4518_ = crate::leanh::lean_box(1);
                if v_isShared_4517_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4516_, 0);
                    crate::leanh::lean_ctor_set(v___x_4516_, 0, v___x_4518_);
                    v___x_4520_ = v___x_4516_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
                    v___x_4520_ = v_reuseFailAlloc_4521_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(
    mut v_pu_4525_: *mut crate::leanh::LeanObject,
    mut v_e_4526_: *mut crate::leanh::LeanObject,
    mut v_a_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v_a_4529_: *mut crate::leanh::LeanObject,
    mut v_a_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
    mut v_a_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4534_: u8 = 0;
    let mut v_a_boxed_4535_: u8 = 0;
    let mut v_res_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4534_ = (crate::leanh::lean_unbox(v_pu_4525_) as u8);
    v_a_boxed_4535_ = (crate::leanh::lean_unbox(v_a_4527_) as u8);
    v_res_4536_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_boxed_4534_, v_e_4526_, v_a_boxed_4535_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
    crate::leanh::lean_dec(v_a_4532_);
    crate::leanh::lean_dec_ref(v_a_4531_);
    crate::leanh::lean_dec(v_a_4530_);
    crate::leanh::lean_dec_ref(v_a_4529_);
    crate::leanh::lean_dec(v_a_4528_);
    return v_res_4536_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(
    mut v_pu_4537_: u8,
    mut v_decl_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: u8,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
    mut v_a_4542_: *mut crate::leanh::LeanObject,
    mut v_a_4543_: *mut crate::leanh::LeanObject,
    mut v_a_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4569_: u8 = 0;
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4581_: u8 = 0;
    let mut v_isSharedCheck_4582_: u8 = 0;
    let mut v_a_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4586_: u8 = 0;
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4590_: u8 = 0;
    let mut v_a_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4594_: u8 = 0;
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v_a_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4606_: u8 = 0;
    let mut v_isSharedCheck_4607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4546_ = crate::leanh::lean_ctor_get(v_decl_4538_, 0);
                v_binderName_4547_ = crate::leanh::lean_ctor_get(v_decl_4538_, 1);
                v_type_4548_ = crate::leanh::lean_ctor_get(v_decl_4538_, 2);
                v_value_4549_ = crate::leanh::lean_ctor_get(v_decl_4538_, 3);
                v_isSharedCheck_4607_ = (!crate::leanh::lean_is_exclusive(v_decl_4538_)) as u8;
                if v_isSharedCheck_4607_ == 0 {
                    v___x_4551_ = v_decl_4538_;
                    v_isShared_4552_ = v_isSharedCheck_4607_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_value_4549_);
                    crate::leanh::lean_inc(v_type_4548_);
                    crate::leanh::lean_inc(v_binderName_4547_);
                    crate::leanh::lean_inc(v_fvarId_4546_);
                    crate::leanh::lean_dec(v_decl_4538_);
                    v___x_4551_ = crate::leanh::lean_box(0);
                    v_isShared_4552_ = v_isSharedCheck_4607_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4553_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_4547_, v_a_4539_, v_a_4542_);
                v_a_4554_ = crate::leanh::lean_ctor_get(v___x_4553_, 0);
                crate::leanh::lean_inc(v_a_4554_);
                crate::leanh::lean_dec_ref(v___x_4553_);
                v___x_4555_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_4537_, v_type_4548_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
                if crate::leanh::lean_obj_tag(v___x_4555_) == 0 {
                    v_a_4556_ = crate::leanh::lean_ctor_get(v___x_4555_, 0);
                    crate::leanh::lean_inc(v_a_4556_);
                    crate::leanh::lean_dec_ref_known(v___x_4555_, 1);
                    v___x_4557_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(v_pu_4537_, v_value_4549_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
                    if crate::leanh::lean_obj_tag(v___x_4557_) == 0 {
                        v_a_4558_ = crate::leanh::lean_ctor_get(v___x_4557_, 0);
                        crate::leanh::lean_inc(v_a_4558_);
                        crate::leanh::lean_dec_ref_known(v___x_4557_, 1);
                        v___x_4559_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_4546_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
                        if crate::leanh::lean_obj_tag(v___x_4559_) == 0 {
                            v_a_4560_ = crate::leanh::lean_ctor_get(v___x_4559_, 0);
                            v_isSharedCheck_4582_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4559_)) as u8;
                            if v_isSharedCheck_4582_ == 0 {
                                v___x_4562_ = v___x_4559_;
                                v_isShared_4563_ = v_isSharedCheck_4582_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4560_);
                                crate::leanh::lean_dec(v___x_4559_);
                                v___x_4562_ = crate::leanh::lean_box(0);
                                v_isShared_4563_ = v_isSharedCheck_4582_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4558_);
                            crate::leanh::lean_dec(v_a_4556_);
                            crate::leanh::lean_dec(v_a_4554_);
                            crate::leanh::lean_del_object(v___x_4551_);
                            v_a_4583_ = crate::leanh::lean_ctor_get(v___x_4559_, 0);
                            v_isSharedCheck_4590_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4559_)) as u8;
                            if v_isSharedCheck_4590_ == 0 {
                                v___x_4585_ = v___x_4559_;
                                v_isShared_4586_ = v_isSharedCheck_4590_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4583_);
                                crate::leanh::lean_dec(v___x_4559_);
                                v___x_4585_ = crate::leanh::lean_box(0);
                                v_isShared_4586_ = v_isSharedCheck_4590_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4556_);
                        crate::leanh::lean_dec(v_a_4554_);
                        crate::leanh::lean_del_object(v___x_4551_);
                        crate::leanh::lean_dec(v_fvarId_4546_);
                        v_a_4591_ = crate::leanh::lean_ctor_get(v___x_4557_, 0);
                        v_isSharedCheck_4598_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4557_)) as u8;
                        if v_isSharedCheck_4598_ == 0 {
                            v___x_4593_ = v___x_4557_;
                            v_isShared_4594_ = v_isSharedCheck_4598_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4591_);
                            crate::leanh::lean_dec(v___x_4557_);
                            v___x_4593_ = crate::leanh::lean_box(0);
                            v_isShared_4594_ = v_isSharedCheck_4598_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4554_);
                    crate::leanh::lean_del_object(v___x_4551_);
                    crate::leanh::lean_dec(v_value_4549_);
                    crate::leanh::lean_dec(v_fvarId_4546_);
                    v_a_4599_ = crate::leanh::lean_ctor_get(v___x_4555_, 0);
                    v_isSharedCheck_4606_ = (!crate::leanh::lean_is_exclusive(v___x_4555_)) as u8;
                    if v_isSharedCheck_4606_ == 0 {
                        v___x_4601_ = v___x_4555_;
                        v_isShared_4602_ = v_isSharedCheck_4606_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4599_);
                        crate::leanh::lean_dec(v___x_4555_);
                        v___x_4601_ = crate::leanh::lean_box(0);
                        v_isShared_4602_ = v_isSharedCheck_4606_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4564_ = lean_st_ref_take(v_a_4542_);
                v_lctx_4565_ = crate::leanh::lean_ctor_get(v___x_4564_, 0);
                v_nextIdx_4566_ = crate::leanh::lean_ctor_get(v___x_4564_, 1);
                v_isSharedCheck_4581_ = (!crate::leanh::lean_is_exclusive(v___x_4564_)) as u8;
                if v_isSharedCheck_4581_ == 0 {
                    v___x_4568_ = v___x_4564_;
                    v_isShared_4569_ = v_isSharedCheck_4581_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_4566_);
                    crate::leanh::lean_inc(v_lctx_4565_);
                    crate::leanh::lean_dec(v___x_4564_);
                    v___x_4568_ = crate::leanh::lean_box(0);
                    v_isShared_4569_ = v_isSharedCheck_4581_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4552_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4551_, 3, v_a_4558_);
                    crate::leanh::lean_ctor_set(v___x_4551_, 2, v_a_4556_);
                    crate::leanh::lean_ctor_set(v___x_4551_, 1, v_a_4554_);
                    crate::leanh::lean_ctor_set(v___x_4551_, 0, v_a_4560_);
                    v___x_4571_ = v___x_4551_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4580_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 1, v_a_4554_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 2, v_a_4556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 3, v_a_4558_);
                    v___x_4571_ = v_reuseFailAlloc_4580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_4571_);
                v___x_4572_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_4537_, v_lctx_4565_, v___x_4571_);
                if v_isShared_4569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4568_, 0, v___x_4572_);
                    v___x_4574_ = v___x_4568_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4579_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4579_, 1, v_nextIdx_4566_);
                    v___x_4574_ = v_reuseFailAlloc_4579_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4575_ = lean_st_ref_set(v_a_4542_, v___x_4574_);
                if v_isShared_4563_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4562_, 0, v___x_4571_);
                    v___x_4577_ = v___x_4562_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4578_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4571_);
                    v___x_4577_ = v_reuseFailAlloc_4578_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4577_;
            }
            7 => {
                if v_isShared_4586_ == 0 {
                    v___x_4588_ = v___x_4585_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
                    v___x_4588_ = v_reuseFailAlloc_4589_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4588_;
            }
            9 => {
                if v_isShared_4594_ == 0 {
                    v___x_4596_ = v___x_4593_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
                    v___x_4596_ = v_reuseFailAlloc_4597_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4596_;
            }
            11 => {
                if v_isShared_4602_ == 0 {
                    v___x_4604_ = v___x_4601_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4605_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
                    v___x_4604_ = v_reuseFailAlloc_4605_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(
    mut v_pu_4608_: *mut crate::leanh::LeanObject,
    mut v_decl_4609_: *mut crate::leanh::LeanObject,
    mut v_a_4610_: *mut crate::leanh::LeanObject,
    mut v_a_4611_: *mut crate::leanh::LeanObject,
    mut v_a_4612_: *mut crate::leanh::LeanObject,
    mut v_a_4613_: *mut crate::leanh::LeanObject,
    mut v_a_4614_: *mut crate::leanh::LeanObject,
    mut v_a_4615_: *mut crate::leanh::LeanObject,
    mut v_a_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4617_: u8 = 0;
    let mut v_a_boxed_4618_: u8 = 0;
    let mut v_res_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4617_ = (crate::leanh::lean_unbox(v_pu_4608_) as u8);
    v_a_boxed_4618_ = (crate::leanh::lean_unbox(v_a_4610_) as u8);
    v_res_4619_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(
        v_pu_boxed_4617_,
        v_decl_4609_,
        v_a_boxed_4618_,
        v_a_4611_,
        v_a_4612_,
        v_a_4613_,
        v_a_4614_,
        v_a_4615_,
    );
    crate::leanh::lean_dec(v_a_4615_);
    crate::leanh::lean_dec_ref(v_a_4614_);
    crate::leanh::lean_dec(v_a_4613_);
    crate::leanh::lean_dec_ref(v_a_4612_);
    crate::leanh::lean_dec(v_a_4611_);
    return v_res_4619_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(
    mut v_pu_4620_: u8,
    mut v_sz_4621_: usize,
    mut v_i_4622_: usize,
    mut v_bs_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: u8,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4631_: u8 = 0;
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: usize = 0;
    let mut v___x_4639_: usize = 0;
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4645_: u8 = 0;
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4631_ = lean_usize_dec_lt(v_i_4622_, v_sz_4621_);
                if v___x_4631_ == 0 {
                    v___x_4632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4632_, 0, v_bs_4623_);
                    return v___x_4632_;
                } else {
                    v_v_4633_ = lean_array_uget_borrowed(v_bs_4623_, v_i_4622_);
                    crate::leanh::lean_inc(v_v_4633_);
                    v___x_4634_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(
                        v_pu_4620_,
                        v_v_4633_,
                        v___y_4624_,
                        v___y_4625_,
                        v___y_4626_,
                        v___y_4627_,
                        v___y_4628_,
                        v___y_4629_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4634_) == 0 {
                        v_a_4635_ = crate::leanh::lean_ctor_get(v___x_4634_, 0);
                        crate::leanh::lean_inc(v_a_4635_);
                        crate::leanh::lean_dec_ref_known(v___x_4634_, 1);
                        v___x_4636_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4637_ = lean_array_uset(v_bs_4623_, v_i_4622_, v___x_4636_);
                        v___x_4638_ = 1usize;
                        v___x_4639_ = lean_usize_add(v_i_4622_, v___x_4638_);
                        v___x_4640_ = lean_array_uset(v_bs_x27_4637_, v_i_4622_, v_a_4635_);
                        v_i_4622_ = v___x_4639_;
                        v_bs_4623_ = v___x_4640_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_4623_);
                        v_a_4642_ = crate::leanh::lean_ctor_get(v___x_4634_, 0);
                        v_isSharedCheck_4649_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4634_)) as u8;
                        if v_isSharedCheck_4649_ == 0 {
                            v___x_4644_ = v___x_4634_;
                            v_isShared_4645_ = v_isSharedCheck_4649_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4642_);
                            crate::leanh::lean_dec(v___x_4634_);
                            v___x_4644_ = crate::leanh::lean_box(0);
                            v_isShared_4645_ = v_isSharedCheck_4649_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4645_ == 0 {
                    v___x_4647_ = v___x_4644_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4648_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_a_4642_);
                    v___x_4647_ = v_reuseFailAlloc_4648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(
    mut v_pu_4650_: *mut crate::leanh::LeanObject,
    mut v_sz_4651_: *mut crate::leanh::LeanObject,
    mut v_i_4652_: *mut crate::leanh::LeanObject,
    mut v_bs_4653_: *mut crate::leanh::LeanObject,
    mut v___y_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4661_: u8 = 0;
    let mut v_sz_boxed_4662_: usize = 0;
    let mut v_i_boxed_4663_: usize = 0;
    let mut v___y_26868__boxed_4664_: u8 = 0;
    let mut v_res_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4661_ = (crate::leanh::lean_unbox(v_pu_4650_) as u8);
    v_sz_boxed_4662_ = crate::leanh::lean_unbox_usize(v_sz_4651_);
    crate::leanh::lean_dec(v_sz_4651_);
    v_i_boxed_4663_ = crate::leanh::lean_unbox_usize(v_i_4652_);
    crate::leanh::lean_dec(v_i_4652_);
    v___y_26868__boxed_4664_ = (crate::leanh::lean_unbox(v___y_4654_) as u8);
    v_res_4665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_boxed_4661_, v_sz_boxed_4662_, v_i_boxed_4663_, v_bs_4653_, v___y_26868__boxed_4664_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
    crate::leanh::lean_dec(v___y_4659_);
    crate::leanh::lean_dec_ref(v___y_4658_);
    crate::leanh::lean_dec(v___y_4657_);
    crate::leanh::lean_dec_ref(v___y_4656_);
    crate::leanh::lean_dec(v___y_4655_);
    return v_res_4665_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(
    mut v_pu_4666_: u8,
    mut v_sz_4667_: usize,
    mut v_i_4668_: usize,
    mut v_bs_4669_: *mut crate::leanh::LeanObject,
    mut v___y_4670_: u8,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
    mut v___y_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: usize = 0;
    let mut v___x_4685_: usize = 0;
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4693_: u8 = 0;
    let mut v_sz_4694_: usize = 0;
    let mut v___x_4695_: usize = 0;
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4710_: u8 = 0;
    let mut v_isSharedCheck_4711_: u8 = 0;
    let mut v_info_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4716_: u8 = 0;
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4729_: u8 = 0;
    let mut v_isSharedCheck_4730_: u8 = 0;
    let mut v_code_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4734_: u8 = 0;
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4743_: u8 = 0;
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4747_: u8 = 0;
    let mut v_isSharedCheck_4748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4677_ = lean_usize_dec_lt(v_i_4668_, v_sz_4667_);
                if v___x_4677_ == 0 {
                    v___x_4678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4678_, 0, v_bs_4669_);
                    return v___x_4678_;
                } else {
                    v_v_4679_ = lean_array_uget(v_bs_4669_, v_i_4668_);
                    v___x_4680_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4681_ = lean_array_uset(v_bs_4669_, v_i_4668_, v___x_4680_);
                    match crate::leanh::lean_obj_tag(v_v_4679_) {
                        0 => {
                            v_ctorName_4688_ = crate::leanh::lean_ctor_get(v_v_4679_, 0);
                            v_params_4689_ = crate::leanh::lean_ctor_get(v_v_4679_, 1);
                            v_code_4690_ = crate::leanh::lean_ctor_get(v_v_4679_, 2);
                            v_isSharedCheck_4711_ =
                                (!crate::leanh::lean_is_exclusive(v_v_4679_)) as u8;
                            if v_isSharedCheck_4711_ == 0 {
                                v___x_4692_ = v_v_4679_;
                                v_isShared_4693_ = v_isSharedCheck_4711_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_code_4690_);
                                crate::leanh::lean_inc(v_params_4689_);
                                crate::leanh::lean_inc(v_ctorName_4688_);
                                crate::leanh::lean_dec(v_v_4679_);
                                v___x_4692_ = crate::leanh::lean_box(0);
                                v_isShared_4693_ = v_isSharedCheck_4711_;
                                state = 2;
                                continue;
                            }
                        }
                        1 => {
                            v_info_4712_ = crate::leanh::lean_ctor_get(v_v_4679_, 0);
                            v_code_4713_ = crate::leanh::lean_ctor_get(v_v_4679_, 1);
                            v_isSharedCheck_4730_ =
                                (!crate::leanh::lean_is_exclusive(v_v_4679_)) as u8;
                            if v_isSharedCheck_4730_ == 0 {
                                v___x_4715_ = v_v_4679_;
                                v_isShared_4716_ = v_isSharedCheck_4730_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_code_4713_);
                                crate::leanh::lean_inc(v_info_4712_);
                                crate::leanh::lean_dec(v_v_4679_);
                                v___x_4715_ = crate::leanh::lean_box(0);
                                v_isShared_4716_ = v_isSharedCheck_4730_;
                                state = 6;
                                continue;
                            }
                        }
                        _ => {
                            v_code_4731_ = crate::leanh::lean_ctor_get(v_v_4679_, 0);
                            v_isSharedCheck_4748_ =
                                (!crate::leanh::lean_is_exclusive(v_v_4679_)) as u8;
                            if v_isSharedCheck_4748_ == 0 {
                                v___x_4733_ = v_v_4679_;
                                v_isShared_4734_ = v_isSharedCheck_4748_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_code_4731_);
                                crate::leanh::lean_dec(v_v_4679_);
                                v___x_4733_ = crate::leanh::lean_box(0);
                                v_isShared_4734_ = v_isSharedCheck_4748_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4684_ = 1usize;
                v___x_4685_ = lean_usize_add(v_i_4668_, v___x_4684_);
                v___x_4686_ = lean_array_uset(v_bs_x27_4681_, v_i_4668_, v_a_4683_);
                v_i_4668_ = v___x_4685_;
                v_bs_4669_ = v___x_4686_;
                state = 0;
                continue;
            }
            2 => {
                v_sz_4694_ = lean_array_size(v_params_4689_);
                v___x_4695_ = 0usize;
                v___x_4696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_4666_, v_sz_4694_, v___x_4695_, v_params_4689_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
                if crate::leanh::lean_obj_tag(v___x_4696_) == 0 {
                    v_a_4697_ = crate::leanh::lean_ctor_get(v___x_4696_, 0);
                    crate::leanh::lean_inc(v_a_4697_);
                    crate::leanh::lean_dec_ref_known(v___x_4696_, 1);
                    v___x_4698_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                        v_pu_4666_,
                        v_code_4690_,
                        v___y_4670_,
                        v___y_4671_,
                        v___y_4672_,
                        v___y_4673_,
                        v___y_4674_,
                        v___y_4675_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4698_) == 0 {
                        v_a_4699_ = crate::leanh::lean_ctor_get(v___x_4698_, 0);
                        crate::leanh::lean_inc(v_a_4699_);
                        crate::leanh::lean_dec_ref_known(v___x_4698_, 1);
                        if v_isShared_4693_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4692_, 2, v_a_4699_);
                            crate::leanh::lean_ctor_set(v___x_4692_, 1, v_a_4697_);
                            v___x_4701_ = v___x_4692_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4702_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4702_,
                                0,
                                v_ctorName_4688_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 1, v_a_4697_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 2, v_a_4699_);
                            v___x_4701_ = v_reuseFailAlloc_4702_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4697_);
                        crate::leanh::lean_del_object(v___x_4692_);
                        crate::leanh::lean_dec(v_ctorName_4688_);
                        crate::leanh::lean_dec_ref(v_bs_x27_4681_);
                        v_a_4703_ = crate::leanh::lean_ctor_get(v___x_4698_, 0);
                        v_isSharedCheck_4710_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4698_)) as u8;
                        if v_isSharedCheck_4710_ == 0 {
                            v___x_4705_ = v___x_4698_;
                            v_isShared_4706_ = v_isSharedCheck_4710_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4703_);
                            crate::leanh::lean_dec(v___x_4698_);
                            v___x_4705_ = crate::leanh::lean_box(0);
                            v_isShared_4706_ = v_isSharedCheck_4710_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4692_);
                    crate::leanh::lean_dec_ref(v_code_4690_);
                    crate::leanh::lean_dec(v_ctorName_4688_);
                    crate::leanh::lean_dec_ref(v_bs_x27_4681_);
                    return v___x_4696_;
                }
            }
            3 => {
                v_a_4683_ = v___x_4701_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_4706_ == 0 {
                    v___x_4708_ = v___x_4705_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
                    v___x_4708_ = v_reuseFailAlloc_4709_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4708_;
            }
            6 => {
                v___x_4717_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                    v_pu_4666_,
                    v_code_4713_,
                    v___y_4670_,
                    v___y_4671_,
                    v___y_4672_,
                    v___y_4673_,
                    v___y_4674_,
                    v___y_4675_,
                );
                if crate::leanh::lean_obj_tag(v___x_4717_) == 0 {
                    v_a_4718_ = crate::leanh::lean_ctor_get(v___x_4717_, 0);
                    crate::leanh::lean_inc(v_a_4718_);
                    crate::leanh::lean_dec_ref_known(v___x_4717_, 1);
                    if v_isShared_4716_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4715_, 1, v_a_4718_);
                        v___x_4720_ = v___x_4715_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4721_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_info_4712_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4721_, 1, v_a_4718_);
                        v___x_4720_ = v_reuseFailAlloc_4721_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4715_);
                    crate::leanh::lean_dec_ref(v_info_4712_);
                    crate::leanh::lean_dec_ref(v_bs_x27_4681_);
                    v_a_4722_ = crate::leanh::lean_ctor_get(v___x_4717_, 0);
                    v_isSharedCheck_4729_ = (!crate::leanh::lean_is_exclusive(v___x_4717_)) as u8;
                    if v_isSharedCheck_4729_ == 0 {
                        v___x_4724_ = v___x_4717_;
                        v_isShared_4725_ = v_isSharedCheck_4729_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4722_);
                        crate::leanh::lean_dec(v___x_4717_);
                        v___x_4724_ = crate::leanh::lean_box(0);
                        v_isShared_4725_ = v_isSharedCheck_4729_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                v_a_4683_ = v___x_4720_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_4725_ == 0 {
                    v___x_4727_ = v___x_4724_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4728_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
                    v___x_4727_ = v_reuseFailAlloc_4728_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4727_;
            }
            10 => {
                v___x_4735_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                    v_pu_4666_,
                    v_code_4731_,
                    v___y_4670_,
                    v___y_4671_,
                    v___y_4672_,
                    v___y_4673_,
                    v___y_4674_,
                    v___y_4675_,
                );
                if crate::leanh::lean_obj_tag(v___x_4735_) == 0 {
                    v_a_4736_ = crate::leanh::lean_ctor_get(v___x_4735_, 0);
                    crate::leanh::lean_inc(v_a_4736_);
                    crate::leanh::lean_dec_ref_known(v___x_4735_, 1);
                    if v_isShared_4734_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4733_, 0, v_a_4736_);
                        v___x_4738_ = v___x_4733_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4739_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4736_);
                        v___x_4738_ = v_reuseFailAlloc_4739_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4733_);
                    crate::leanh::lean_dec_ref(v_bs_x27_4681_);
                    v_a_4740_ = crate::leanh::lean_ctor_get(v___x_4735_, 0);
                    v_isSharedCheck_4747_ = (!crate::leanh::lean_is_exclusive(v___x_4735_)) as u8;
                    if v_isSharedCheck_4747_ == 0 {
                        v___x_4742_ = v___x_4735_;
                        v_isShared_4743_ = v_isSharedCheck_4747_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4740_);
                        crate::leanh::lean_dec(v___x_4735_);
                        v___x_4742_ = crate::leanh::lean_box(0);
                        v_isShared_4743_ = v_isSharedCheck_4747_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                v_a_4683_ = v___x_4738_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_4743_ == 0 {
                    v___x_4745_ = v___x_4742_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
                    v___x_4745_ = v_reuseFailAlloc_4746_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeCode(
    mut v_pu_4749_: u8,
    mut v_code_4750_: *mut crate::leanh::LeanObject,
    mut v_a_4751_: u8,
    mut v_a_4752_: *mut crate::leanh::LeanObject,
    mut v_a_4753_: *mut crate::leanh::LeanObject,
    mut v_a_4754_: *mut crate::leanh::LeanObject,
    mut v_a_4755_: *mut crate::leanh::LeanObject,
    mut v_a_4756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4776_: u8 = 0;
    let mut v_a_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4780_: u8 = 0;
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4784_: u8 = 0;
    let mut v_isSharedCheck_4785_: u8 = 0;
    let mut v_decl_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4790_: u8 = 0;
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4797_: u8 = 0;
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4804_: u8 = 0;
    let mut v_a_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4808_: u8 = 0;
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4812_: u8 = 0;
    let mut v_isSharedCheck_4813_: u8 = 0;
    let mut v_decl_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4818_: u8 = 0;
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4832_: u8 = 0;
    let mut v_a_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4840_: u8 = 0;
    let mut v_isSharedCheck_4841_: u8 = 0;
    let mut v_fvarId_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4846_: u8 = 0;
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: u8 = 0;
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4862_: u8 = 0;
    let mut v_a_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4870_: u8 = 0;
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut v_cases_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4876_: u8 = 0;
    let mut v_typeName_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4883_: u8 = 0;
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: u8 = 0;
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4890_: usize = 0;
    let mut v___x_4891_: usize = 0;
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4896_: u8 = 0;
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4906_: u8 = 0;
    let mut v_a_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4910_: u8 = 0;
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4914_: u8 = 0;
    let mut v_a_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4922_: u8 = 0;
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4924_: u8 = 0;
    let mut v_isSharedCheck_4925_: u8 = 0;
    let mut v_fvarId_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4929_: u8 = 0;
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: u8 = 0;
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4943_: u8 = 0;
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4945_: u8 = 0;
    let mut v_type_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4949_: u8 = 0;
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4954_: u8 = 0;
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4961_: u8 = 0;
    let mut v_a_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4969_: u8 = 0;
    let mut v_isSharedCheck_4970_: u8 = 0;
    let mut v_fvarId_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4977_: u8 = 0;
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: u8 = 0;
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4988_: u8 = 0;
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4995_: u8 = 0;
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut v_fvarId_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5004_: u8 = 0;
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: u8 = 0;
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5016_: u8 = 0;
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5026_: u8 = 0;
    let mut v_fvarId_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: u8 = 0;
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5049_: u8 = 0;
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5056_: u8 = 0;
    let mut v_a_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5060_: u8 = 0;
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5064_: u8 = 0;
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5067_: u8 = 0;
    let mut v_fvarId_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5073_: u8 = 0;
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: u8 = 0;
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5082_: u8 = 0;
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5089_: u8 = 0;
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5091_: u8 = 0;
    let mut v_fvarId_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_5094_: u8 = 0;
    let mut v_persistent_5095_: u8 = 0;
    let mut v_k_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5099_: u8 = 0;
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: u8 = 0;
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5108_: u8 = 0;
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5115_: u8 = 0;
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5117_: u8 = 0;
    let mut v_fvarId_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_5120_: u8 = 0;
    let mut v_persistent_5121_: u8 = 0;
    let mut v_objs_x3f_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5126_: u8 = 0;
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: u8 = 0;
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5135_: u8 = 0;
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5144_: u8 = 0;
    let mut v_fvarId_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5149_: u8 = 0;
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: u8 = 0;
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5158_: u8 = 0;
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5165_: u8 = 0;
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_4750_) {
                0 => {
                    v_decl_4758_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_k_4759_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_isSharedCheck_4785_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_4785_ == 0 {
                        v___x_4761_ = v_code_4750_;
                        v_isShared_4762_ = v_isSharedCheck_4785_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4759_);
                        crate::leanh::lean_inc(v_decl_4758_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_4761_ = crate::leanh::lean_box(0);
                        v_isShared_4762_ = v_isSharedCheck_4785_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_decl_4786_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_k_4787_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_isSharedCheck_4813_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_4813_ == 0 {
                        v___x_4789_ = v_code_4750_;
                        v_isShared_4790_ = v_isSharedCheck_4813_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4787_);
                        crate::leanh::lean_inc(v_decl_4786_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_4789_ = crate::leanh::lean_box(0);
                        v_isShared_4790_ = v_isSharedCheck_4813_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_decl_4814_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_k_4815_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_isSharedCheck_4841_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_4841_ == 0 {
                        v___x_4817_ = v_code_4750_;
                        v_isShared_4818_ = v_isSharedCheck_4841_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4815_);
                        crate::leanh::lean_inc(v_decl_4814_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_4817_ = crate::leanh::lean_box(0);
                        v_isShared_4818_ = v_isSharedCheck_4841_;
                        state = 13;
                        continue;
                    }
                }
                3 => {
                    v_fvarId_4842_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_args_4843_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_isSharedCheck_4872_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_4872_ == 0 {
                        v___x_4845_ = v_code_4750_;
                        v_isShared_4846_ = v_isSharedCheck_4872_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_4843_);
                        crate::leanh::lean_inc(v_fvarId_4842_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_4845_ = crate::leanh::lean_box(0);
                        v_isShared_4846_ = v_isSharedCheck_4872_;
                        state = 19;
                        continue;
                    }
                }
                4 => {
                    v_cases_4873_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_isSharedCheck_4925_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_4925_ == 0 {
                        v___x_4875_ = v_code_4750_;
                        v_isShared_4876_ = v_isSharedCheck_4925_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_4873_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_4875_ = crate::leanh::lean_box(0);
                        v_isShared_4876_ = v_isSharedCheck_4925_;
                        state = 25;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_4926_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_isSharedCheck_4945_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_4945_ == 0 {
                        v___x_4928_ = v_code_4750_;
                        v_isShared_4929_ = v_isSharedCheck_4945_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_4926_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_4928_ = crate::leanh::lean_box(0);
                        v_isShared_4929_ = v_isSharedCheck_4945_;
                        state = 35;
                        continue;
                    }
                }
                6 => {
                    v_type_4946_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_isSharedCheck_4970_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_4970_ == 0 {
                        v___x_4948_ = v_code_4750_;
                        v_isShared_4949_ = v_isSharedCheck_4970_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_type_4946_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_4948_ = crate::leanh::lean_box(0);
                        v_isShared_4949_ = v_isSharedCheck_4970_;
                        state = 39;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_4971_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_i_4972_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_y_4973_ = crate::leanh::lean_ctor_get(v_code_4750_, 2);
                    v_k_4974_ = crate::leanh::lean_ctor_get(v_code_4750_, 3);
                    v_isSharedCheck_4997_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_4997_ == 0 {
                        v___x_4976_ = v_code_4750_;
                        v_isShared_4977_ = v_isSharedCheck_4997_;
                        state = 45;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4974_);
                        crate::leanh::lean_inc(v_y_4973_);
                        crate::leanh::lean_inc(v_i_4972_);
                        crate::leanh::lean_inc(v_fvarId_4971_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_4976_ = crate::leanh::lean_box(0);
                        v_isShared_4977_ = v_isSharedCheck_4997_;
                        state = 45;
                        continue;
                    }
                }
                8 => {
                    v_fvarId_4998_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_i_4999_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_y_5000_ = crate::leanh::lean_ctor_get(v_code_4750_, 2);
                    v_k_5001_ = crate::leanh::lean_ctor_get(v_code_4750_, 3);
                    v_isSharedCheck_5026_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_5026_ == 0 {
                        v___x_5003_ = v_code_4750_;
                        v_isShared_5004_ = v_isSharedCheck_5026_;
                        state = 49;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5001_);
                        crate::leanh::lean_inc(v_y_5000_);
                        crate::leanh::lean_inc(v_i_4999_);
                        crate::leanh::lean_inc(v_fvarId_4998_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_5003_ = crate::leanh::lean_box(0);
                        v_isShared_5004_ = v_isSharedCheck_5026_;
                        state = 49;
                        continue;
                    }
                }
                9 => {
                    v_fvarId_5027_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_i_5028_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_offset_5029_ = crate::leanh::lean_ctor_get(v_code_4750_, 2);
                    v_y_5030_ = crate::leanh::lean_ctor_get(v_code_4750_, 3);
                    v_ty_5031_ = crate::leanh::lean_ctor_get(v_code_4750_, 4);
                    v_k_5032_ = crate::leanh::lean_ctor_get(v_code_4750_, 5);
                    v_isSharedCheck_5067_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_5067_ == 0 {
                        v___x_5034_ = v_code_4750_;
                        v_isShared_5035_ = v_isSharedCheck_5067_;
                        state = 53;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5032_);
                        crate::leanh::lean_inc(v_ty_5031_);
                        crate::leanh::lean_inc(v_y_5030_);
                        crate::leanh::lean_inc(v_offset_5029_);
                        crate::leanh::lean_inc(v_i_5028_);
                        crate::leanh::lean_inc(v_fvarId_5027_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_5034_ = crate::leanh::lean_box(0);
                        v_isShared_5035_ = v_isSharedCheck_5067_;
                        state = 53;
                        continue;
                    }
                }
                10 => {
                    v_fvarId_5068_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_cidx_5069_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_k_5070_ = crate::leanh::lean_ctor_get(v_code_4750_, 2);
                    v_isSharedCheck_5091_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_5091_ == 0 {
                        v___x_5072_ = v_code_4750_;
                        v_isShared_5073_ = v_isSharedCheck_5091_;
                        state = 59;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5070_);
                        crate::leanh::lean_inc(v_cidx_5069_);
                        crate::leanh::lean_inc(v_fvarId_5068_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_5072_ = crate::leanh::lean_box(0);
                        v_isShared_5073_ = v_isSharedCheck_5091_;
                        state = 59;
                        continue;
                    }
                }
                11 => {
                    v_fvarId_5092_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_n_5093_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_check_5094_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_4750_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_5095_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_4750_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_5096_ = crate::leanh::lean_ctor_get(v_code_4750_, 2);
                    v_isSharedCheck_5117_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_5117_ == 0 {
                        v___x_5098_ = v_code_4750_;
                        v_isShared_5099_ = v_isSharedCheck_5117_;
                        state = 63;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5096_);
                        crate::leanh::lean_inc(v_n_5093_);
                        crate::leanh::lean_inc(v_fvarId_5092_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_5098_ = crate::leanh::lean_box(0);
                        v_isShared_5099_ = v_isSharedCheck_5117_;
                        state = 63;
                        continue;
                    }
                }
                12 => {
                    v_fvarId_5118_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_n_5119_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_check_5120_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_4750_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_5121_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_4750_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_5122_ = crate::leanh::lean_ctor_get(v_code_4750_, 2);
                    v_k_5123_ = crate::leanh::lean_ctor_get(v_code_4750_, 3);
                    v_isSharedCheck_5144_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_5144_ == 0 {
                        v___x_5125_ = v_code_4750_;
                        v_isShared_5126_ = v_isSharedCheck_5144_;
                        state = 67;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5123_);
                        crate::leanh::lean_inc(v_objs_x3f_5122_);
                        crate::leanh::lean_inc(v_n_5119_);
                        crate::leanh::lean_inc(v_fvarId_5118_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_5125_ = crate::leanh::lean_box(0);
                        v_isShared_5126_ = v_isSharedCheck_5144_;
                        state = 67;
                        continue;
                    }
                }
                _ => {
                    v_fvarId_5145_ = crate::leanh::lean_ctor_get(v_code_4750_, 0);
                    v_k_5146_ = crate::leanh::lean_ctor_get(v_code_4750_, 1);
                    v_isSharedCheck_5167_ = (!crate::leanh::lean_is_exclusive(v_code_4750_)) as u8;
                    if v_isSharedCheck_5167_ == 0 {
                        v___x_5148_ = v_code_4750_;
                        v_isShared_5149_ = v_isSharedCheck_5167_;
                        state = 71;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5146_);
                        crate::leanh::lean_inc(v_fvarId_5145_);
                        crate::leanh::lean_dec(v_code_4750_);
                        v___x_5148_ = crate::leanh::lean_box(0);
                        v_isShared_5149_ = v_isSharedCheck_5167_;
                        state = 71;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4763_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(
                    v_pu_4749_,
                    v_decl_4758_,
                    v_a_4751_,
                    v_a_4752_,
                    v_a_4753_,
                    v_a_4754_,
                    v_a_4755_,
                    v_a_4756_,
                );
                if crate::leanh::lean_obj_tag(v___x_4763_) == 0 {
                    v_a_4764_ = crate::leanh::lean_ctor_get(v___x_4763_, 0);
                    crate::leanh::lean_inc(v_a_4764_);
                    crate::leanh::lean_dec_ref_known(v___x_4763_, 1);
                    v___x_4765_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                        v_pu_4749_, v_k_4759_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                        v_a_4755_, v_a_4756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4765_) == 0 {
                        v_a_4766_ = crate::leanh::lean_ctor_get(v___x_4765_, 0);
                        v_isSharedCheck_4776_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4765_)) as u8;
                        if v_isSharedCheck_4776_ == 0 {
                            v___x_4768_ = v___x_4765_;
                            v_isShared_4769_ = v_isSharedCheck_4776_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4766_);
                            crate::leanh::lean_dec(v___x_4765_);
                            v___x_4768_ = crate::leanh::lean_box(0);
                            v_isShared_4769_ = v_isSharedCheck_4776_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4764_);
                        crate::leanh::lean_del_object(v___x_4761_);
                        return v___x_4765_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4761_);
                    crate::leanh::lean_dec_ref(v_k_4759_);
                    v_a_4777_ = crate::leanh::lean_ctor_get(v___x_4763_, 0);
                    v_isSharedCheck_4784_ = (!crate::leanh::lean_is_exclusive(v___x_4763_)) as u8;
                    if v_isSharedCheck_4784_ == 0 {
                        v___x_4779_ = v___x_4763_;
                        v_isShared_4780_ = v_isSharedCheck_4784_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4777_);
                        crate::leanh::lean_dec(v___x_4763_);
                        v___x_4779_ = crate::leanh::lean_box(0);
                        v_isShared_4780_ = v_isSharedCheck_4784_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4762_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4761_, 1, v_a_4766_);
                    crate::leanh::lean_ctor_set(v___x_4761_, 0, v_a_4764_);
                    v___x_4771_ = v___x_4761_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4775_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4775_, 1, v_a_4766_);
                    v___x_4771_ = v_reuseFailAlloc_4775_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4769_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4768_, 0, v___x_4771_);
                    v___x_4773_ = v___x_4768_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4774_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4771_);
                    v___x_4773_ = v_reuseFailAlloc_4774_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4773_;
            }
            5 => {
                if v_isShared_4780_ == 0 {
                    v___x_4782_ = v___x_4779_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
                    v___x_4782_ = v_reuseFailAlloc_4783_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4782_;
            }
            7 => {
                v___x_4791_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(
                    v_pu_4749_,
                    v_decl_4786_,
                    v_a_4751_,
                    v_a_4752_,
                    v_a_4753_,
                    v_a_4754_,
                    v_a_4755_,
                    v_a_4756_,
                );
                if crate::leanh::lean_obj_tag(v___x_4791_) == 0 {
                    v_a_4792_ = crate::leanh::lean_ctor_get(v___x_4791_, 0);
                    crate::leanh::lean_inc(v_a_4792_);
                    crate::leanh::lean_dec_ref_known(v___x_4791_, 1);
                    v___x_4793_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                        v_pu_4749_, v_k_4787_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                        v_a_4755_, v_a_4756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4793_) == 0 {
                        v_a_4794_ = crate::leanh::lean_ctor_get(v___x_4793_, 0);
                        v_isSharedCheck_4804_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4793_)) as u8;
                        if v_isSharedCheck_4804_ == 0 {
                            v___x_4796_ = v___x_4793_;
                            v_isShared_4797_ = v_isSharedCheck_4804_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4794_);
                            crate::leanh::lean_dec(v___x_4793_);
                            v___x_4796_ = crate::leanh::lean_box(0);
                            v_isShared_4797_ = v_isSharedCheck_4804_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4792_);
                        crate::leanh::lean_del_object(v___x_4789_);
                        return v___x_4793_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4789_);
                    crate::leanh::lean_dec_ref(v_k_4787_);
                    v_a_4805_ = crate::leanh::lean_ctor_get(v___x_4791_, 0);
                    v_isSharedCheck_4812_ = (!crate::leanh::lean_is_exclusive(v___x_4791_)) as u8;
                    if v_isSharedCheck_4812_ == 0 {
                        v___x_4807_ = v___x_4791_;
                        v_isShared_4808_ = v_isSharedCheck_4812_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4805_);
                        crate::leanh::lean_dec(v___x_4791_);
                        v___x_4807_ = crate::leanh::lean_box(0);
                        v_isShared_4808_ = v_isSharedCheck_4812_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4790_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4789_, 1, v_a_4794_);
                    crate::leanh::lean_ctor_set(v___x_4789_, 0, v_a_4792_);
                    v___x_4799_ = v___x_4789_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4803_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4803_, 1, v_a_4794_);
                    v___x_4799_ = v_reuseFailAlloc_4803_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4797_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4796_, 0, v___x_4799_);
                    v___x_4801_ = v___x_4796_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4799_);
                    v___x_4801_ = v_reuseFailAlloc_4802_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4801_;
            }
            11 => {
                if v_isShared_4808_ == 0 {
                    v___x_4810_ = v___x_4807_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
                    v___x_4810_ = v_reuseFailAlloc_4811_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4810_;
            }
            13 => {
                v___x_4819_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(
                    v_pu_4749_,
                    v_decl_4814_,
                    v_a_4751_,
                    v_a_4752_,
                    v_a_4753_,
                    v_a_4754_,
                    v_a_4755_,
                    v_a_4756_,
                );
                if crate::leanh::lean_obj_tag(v___x_4819_) == 0 {
                    v_a_4820_ = crate::leanh::lean_ctor_get(v___x_4819_, 0);
                    crate::leanh::lean_inc(v_a_4820_);
                    crate::leanh::lean_dec_ref_known(v___x_4819_, 1);
                    v___x_4821_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                        v_pu_4749_, v_k_4815_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                        v_a_4755_, v_a_4756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4821_) == 0 {
                        v_a_4822_ = crate::leanh::lean_ctor_get(v___x_4821_, 0);
                        v_isSharedCheck_4832_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4821_)) as u8;
                        if v_isSharedCheck_4832_ == 0 {
                            v___x_4824_ = v___x_4821_;
                            v_isShared_4825_ = v_isSharedCheck_4832_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4822_);
                            crate::leanh::lean_dec(v___x_4821_);
                            v___x_4824_ = crate::leanh::lean_box(0);
                            v_isShared_4825_ = v_isSharedCheck_4832_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4820_);
                        crate::leanh::lean_del_object(v___x_4817_);
                        return v___x_4821_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4817_);
                    crate::leanh::lean_dec_ref(v_k_4815_);
                    v_a_4833_ = crate::leanh::lean_ctor_get(v___x_4819_, 0);
                    v_isSharedCheck_4840_ = (!crate::leanh::lean_is_exclusive(v___x_4819_)) as u8;
                    if v_isSharedCheck_4840_ == 0 {
                        v___x_4835_ = v___x_4819_;
                        v_isShared_4836_ = v_isSharedCheck_4840_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4833_);
                        crate::leanh::lean_dec(v___x_4819_);
                        v___x_4835_ = crate::leanh::lean_box(0);
                        v_isShared_4836_ = v_isSharedCheck_4840_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_4818_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4817_, 1, v_a_4822_);
                    crate::leanh::lean_ctor_set(v___x_4817_, 0, v_a_4820_);
                    v___x_4827_ = v___x_4817_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4831_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4831_, 1, v_a_4822_);
                    v___x_4827_ = v_reuseFailAlloc_4831_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_4825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4824_, 0, v___x_4827_);
                    v___x_4829_ = v___x_4824_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
                    v___x_4829_ = v_reuseFailAlloc_4830_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4829_;
            }
            17 => {
                if v_isShared_4836_ == 0 {
                    v___x_4838_ = v___x_4835_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
                    v___x_4838_ = v_reuseFailAlloc_4839_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4838_;
            }
            19 => {
                v___x_4847_ = lean_st_ref_get(v_a_4752_);
                v___x_4848_ = 1;
                v___x_4849_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_4847_,
                    v_fvarId_4842_,
                    v___x_4848_,
                );
                crate::leanh::lean_dec(v___x_4847_);
                if crate::leanh::lean_obj_tag(v___x_4849_) == 0 {
                    v_fvarId_4850_ = crate::leanh::lean_ctor_get(v___x_4849_, 0);
                    crate::leanh::lean_inc(v_fvarId_4850_);
                    crate::leanh::lean_dec_ref_known(v___x_4849_, 1);
                    v___x_4851_ = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(
                        v_pu_4749_,
                        v_args_4843_,
                        v_a_4751_,
                        v_a_4752_,
                        v_a_4753_,
                        v_a_4754_,
                        v_a_4755_,
                        v_a_4756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4851_) == 0 {
                        v_a_4852_ = crate::leanh::lean_ctor_get(v___x_4851_, 0);
                        v_isSharedCheck_4862_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4851_)) as u8;
                        if v_isSharedCheck_4862_ == 0 {
                            v___x_4854_ = v___x_4851_;
                            v_isShared_4855_ = v_isSharedCheck_4862_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4852_);
                            crate::leanh::lean_dec(v___x_4851_);
                            v___x_4854_ = crate::leanh::lean_box(0);
                            v_isShared_4855_ = v_isSharedCheck_4862_;
                            state = 20;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_4850_);
                        crate::leanh::lean_del_object(v___x_4845_);
                        v_a_4863_ = crate::leanh::lean_ctor_get(v___x_4851_, 0);
                        v_isSharedCheck_4870_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4851_)) as u8;
                        if v_isSharedCheck_4870_ == 0 {
                            v___x_4865_ = v___x_4851_;
                            v_isShared_4866_ = v_isSharedCheck_4870_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4863_);
                            crate::leanh::lean_dec(v___x_4851_);
                            v___x_4865_ = crate::leanh::lean_box(0);
                            v_isShared_4866_ = v_isSharedCheck_4870_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4845_);
                    crate::leanh::lean_dec_ref(v_args_4843_);
                    v___x_4871_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_4871_;
                }
            }
            20 => {
                if v_isShared_4846_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4845_, 1, v_a_4852_);
                    crate::leanh::lean_ctor_set(v___x_4845_, 0, v_fvarId_4850_);
                    v___x_4857_ = v___x_4845_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_fvarId_4850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 1, v_a_4852_);
                    v___x_4857_ = v_reuseFailAlloc_4861_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_4855_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4854_, 0, v___x_4857_);
                    v___x_4859_ = v___x_4854_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4857_);
                    v___x_4859_ = v_reuseFailAlloc_4860_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4859_;
            }
            23 => {
                if v_isShared_4866_ == 0 {
                    v___x_4868_ = v___x_4865_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
                    v___x_4868_ = v_reuseFailAlloc_4869_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4868_;
            }
            25 => {
                v_typeName_4877_ = crate::leanh::lean_ctor_get(v_cases_4873_, 0);
                v_resultType_4878_ = crate::leanh::lean_ctor_get(v_cases_4873_, 1);
                v_discr_4879_ = crate::leanh::lean_ctor_get(v_cases_4873_, 2);
                v_alts_4880_ = crate::leanh::lean_ctor_get(v_cases_4873_, 3);
                v_isSharedCheck_4924_ = (!crate::leanh::lean_is_exclusive(v_cases_4873_)) as u8;
                if v_isSharedCheck_4924_ == 0 {
                    v___x_4882_ = v_cases_4873_;
                    v_isShared_4883_ = v_isSharedCheck_4924_;
                    state = 26;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_alts_4880_);
                    crate::leanh::lean_inc(v_discr_4879_);
                    crate::leanh::lean_inc(v_resultType_4878_);
                    crate::leanh::lean_inc(v_typeName_4877_);
                    crate::leanh::lean_dec(v_cases_4873_);
                    v___x_4882_ = crate::leanh::lean_box(0);
                    v_isShared_4883_ = v_isSharedCheck_4924_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4884_ = lean_st_ref_get(v_a_4752_);
                v___x_4885_ = 1;
                v___x_4886_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_4884_,
                    v_discr_4879_,
                    v___x_4885_,
                );
                crate::leanh::lean_dec(v___x_4884_);
                if crate::leanh::lean_obj_tag(v___x_4886_) == 0 {
                    v_fvarId_4887_ = crate::leanh::lean_ctor_get(v___x_4886_, 0);
                    crate::leanh::lean_inc(v_fvarId_4887_);
                    crate::leanh::lean_dec_ref_known(v___x_4886_, 1);
                    v___x_4888_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_4749_, v_resultType_4878_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
                    if crate::leanh::lean_obj_tag(v___x_4888_) == 0 {
                        v_a_4889_ = crate::leanh::lean_ctor_get(v___x_4888_, 0);
                        crate::leanh::lean_inc(v_a_4889_);
                        crate::leanh::lean_dec_ref_known(v___x_4888_, 1);
                        v_sz_4890_ = lean_array_size(v_alts_4880_);
                        v___x_4891_ = 0usize;
                        v___x_4892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_4749_, v_sz_4890_, v___x_4891_, v_alts_4880_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
                        if crate::leanh::lean_obj_tag(v___x_4892_) == 0 {
                            v_a_4893_ = crate::leanh::lean_ctor_get(v___x_4892_, 0);
                            v_isSharedCheck_4906_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4892_)) as u8;
                            if v_isSharedCheck_4906_ == 0 {
                                v___x_4895_ = v___x_4892_;
                                v_isShared_4896_ = v_isSharedCheck_4906_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4893_);
                                crate::leanh::lean_dec(v___x_4892_);
                                v___x_4895_ = crate::leanh::lean_box(0);
                                v_isShared_4896_ = v_isSharedCheck_4906_;
                                state = 27;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4889_);
                            crate::leanh::lean_dec(v_fvarId_4887_);
                            crate::leanh::lean_del_object(v___x_4882_);
                            crate::leanh::lean_dec(v_typeName_4877_);
                            crate::leanh::lean_del_object(v___x_4875_);
                            v_a_4907_ = crate::leanh::lean_ctor_get(v___x_4892_, 0);
                            v_isSharedCheck_4914_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4892_)) as u8;
                            if v_isSharedCheck_4914_ == 0 {
                                v___x_4909_ = v___x_4892_;
                                v_isShared_4910_ = v_isSharedCheck_4914_;
                                state = 31;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4907_);
                                crate::leanh::lean_dec(v___x_4892_);
                                v___x_4909_ = crate::leanh::lean_box(0);
                                v_isShared_4910_ = v_isSharedCheck_4914_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_4887_);
                        crate::leanh::lean_del_object(v___x_4882_);
                        crate::leanh::lean_dec_ref(v_alts_4880_);
                        crate::leanh::lean_dec(v_typeName_4877_);
                        crate::leanh::lean_del_object(v___x_4875_);
                        v_a_4915_ = crate::leanh::lean_ctor_get(v___x_4888_, 0);
                        v_isSharedCheck_4922_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4888_)) as u8;
                        if v_isSharedCheck_4922_ == 0 {
                            v___x_4917_ = v___x_4888_;
                            v_isShared_4918_ = v_isSharedCheck_4922_;
                            state = 33;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4915_);
                            crate::leanh::lean_dec(v___x_4888_);
                            v___x_4917_ = crate::leanh::lean_box(0);
                            v_isShared_4918_ = v_isSharedCheck_4922_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4882_);
                    crate::leanh::lean_dec_ref(v_alts_4880_);
                    crate::leanh::lean_dec_ref(v_resultType_4878_);
                    crate::leanh::lean_dec(v_typeName_4877_);
                    crate::leanh::lean_del_object(v___x_4875_);
                    v___x_4923_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_4923_;
                }
            }
            27 => {
                if v_isShared_4883_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4882_, 3, v_a_4893_);
                    crate::leanh::lean_ctor_set(v___x_4882_, 2, v_fvarId_4887_);
                    crate::leanh::lean_ctor_set(v___x_4882_, 1, v_a_4889_);
                    v___x_4898_ = v___x_4882_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4905_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_typeName_4877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4905_, 1, v_a_4889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4905_, 2, v_fvarId_4887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4905_, 3, v_a_4893_);
                    v___x_4898_ = v_reuseFailAlloc_4905_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_4876_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4875_, 0, v___x_4898_);
                    v___x_4900_ = v___x_4875_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4904_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4898_);
                    v___x_4900_ = v_reuseFailAlloc_4904_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_4896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4895_, 0, v___x_4900_);
                    v___x_4902_ = v___x_4895_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4900_);
                    v___x_4902_ = v_reuseFailAlloc_4903_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4902_;
            }
            31 => {
                if v_isShared_4910_ == 0 {
                    v___x_4912_ = v___x_4909_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4913_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4907_);
                    v___x_4912_ = v_reuseFailAlloc_4913_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4912_;
            }
            33 => {
                if v_isShared_4918_ == 0 {
                    v___x_4920_ = v___x_4917_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
                    v___x_4920_ = v_reuseFailAlloc_4921_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4920_;
            }
            35 => {
                v___x_4930_ = lean_st_ref_get(v_a_4752_);
                v___x_4931_ = 1;
                v___x_4932_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_4930_,
                    v_fvarId_4926_,
                    v___x_4931_,
                );
                crate::leanh::lean_dec(v___x_4930_);
                if crate::leanh::lean_obj_tag(v___x_4932_) == 0 {
                    v_fvarId_4933_ = crate::leanh::lean_ctor_get(v___x_4932_, 0);
                    v_isSharedCheck_4943_ = (!crate::leanh::lean_is_exclusive(v___x_4932_)) as u8;
                    if v_isSharedCheck_4943_ == 0 {
                        v___x_4935_ = v___x_4932_;
                        v_isShared_4936_ = v_isSharedCheck_4943_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_4933_);
                        crate::leanh::lean_dec(v___x_4932_);
                        v___x_4935_ = crate::leanh::lean_box(0);
                        v_isShared_4936_ = v_isSharedCheck_4943_;
                        state = 36;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4928_);
                    v___x_4944_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_4944_;
                }
            }
            36 => {
                if v_isShared_4929_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4928_, 0, v_fvarId_4933_);
                    v___x_4938_ = v___x_4928_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4942_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_fvarId_4933_);
                    v___x_4938_ = v_reuseFailAlloc_4942_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_4936_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4935_, 0, v___x_4938_);
                    v___x_4940_ = v___x_4935_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4941_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4938_);
                    v___x_4940_ = v_reuseFailAlloc_4941_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4940_;
            }
            39 => {
                v___x_4950_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_4749_, v_type_4946_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
                if crate::leanh::lean_obj_tag(v___x_4950_) == 0 {
                    v_a_4951_ = crate::leanh::lean_ctor_get(v___x_4950_, 0);
                    v_isSharedCheck_4961_ = (!crate::leanh::lean_is_exclusive(v___x_4950_)) as u8;
                    if v_isSharedCheck_4961_ == 0 {
                        v___x_4953_ = v___x_4950_;
                        v_isShared_4954_ = v_isSharedCheck_4961_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4951_);
                        crate::leanh::lean_dec(v___x_4950_);
                        v___x_4953_ = crate::leanh::lean_box(0);
                        v_isShared_4954_ = v_isSharedCheck_4961_;
                        state = 40;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4948_);
                    v_a_4962_ = crate::leanh::lean_ctor_get(v___x_4950_, 0);
                    v_isSharedCheck_4969_ = (!crate::leanh::lean_is_exclusive(v___x_4950_)) as u8;
                    if v_isSharedCheck_4969_ == 0 {
                        v___x_4964_ = v___x_4950_;
                        v_isShared_4965_ = v_isSharedCheck_4969_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4962_);
                        crate::leanh::lean_dec(v___x_4950_);
                        v___x_4964_ = crate::leanh::lean_box(0);
                        v_isShared_4965_ = v_isSharedCheck_4969_;
                        state = 43;
                        continue;
                    }
                }
            }
            40 => {
                if v_isShared_4949_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4948_, 0, v_a_4951_);
                    v___x_4956_ = v___x_4948_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4960_ = crate::leanh::lean_alloc_ctor(6, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4951_);
                    v___x_4956_ = v_reuseFailAlloc_4960_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_4954_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4953_, 0, v___x_4956_);
                    v___x_4958_ = v___x_4953_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4956_);
                    v___x_4958_ = v_reuseFailAlloc_4959_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4958_;
            }
            43 => {
                if v_isShared_4965_ == 0 {
                    v___x_4967_ = v___x_4964_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
                    v___x_4967_ = v_reuseFailAlloc_4968_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4967_;
            }
            45 => {
                v___x_4978_ = lean_st_ref_get(v_a_4752_);
                v___x_4979_ = 1;
                v___x_4980_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_4978_,
                    v_fvarId_4971_,
                    v___x_4979_,
                );
                crate::leanh::lean_dec(v___x_4978_);
                if crate::leanh::lean_obj_tag(v___x_4980_) == 0 {
                    v_fvarId_4981_ = crate::leanh::lean_ctor_get(v___x_4980_, 0);
                    crate::leanh::lean_inc(v_fvarId_4981_);
                    crate::leanh::lean_dec_ref_known(v___x_4980_, 1);
                    v___x_4982_ = lean_st_ref_get(v_a_4752_);
                    v___x_4983_ =
                        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
                            v_pu_4749_,
                            v___x_4982_,
                            v_y_4973_,
                            v___x_4979_,
                        );
                    crate::leanh::lean_dec(v___x_4982_);
                    v___x_4984_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                        v_pu_4749_, v_k_4974_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                        v_a_4755_, v_a_4756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4984_) == 0 {
                        v_a_4985_ = crate::leanh::lean_ctor_get(v___x_4984_, 0);
                        v_isSharedCheck_4995_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4984_)) as u8;
                        if v_isSharedCheck_4995_ == 0 {
                            v___x_4987_ = v___x_4984_;
                            v_isShared_4988_ = v_isSharedCheck_4995_;
                            state = 46;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4985_);
                            crate::leanh::lean_dec(v___x_4984_);
                            v___x_4987_ = crate::leanh::lean_box(0);
                            v_isShared_4988_ = v_isSharedCheck_4995_;
                            state = 46;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4983_);
                        crate::leanh::lean_dec(v_fvarId_4981_);
                        crate::leanh::lean_del_object(v___x_4976_);
                        crate::leanh::lean_dec(v_i_4972_);
                        return v___x_4984_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4976_);
                    crate::leanh::lean_dec_ref(v_k_4974_);
                    crate::leanh::lean_dec(v_y_4973_);
                    crate::leanh::lean_dec(v_i_4972_);
                    v___x_4996_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_4996_;
                }
            }
            46 => {
                if v_isShared_4977_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4976_, 3, v_a_4985_);
                    crate::leanh::lean_ctor_set(v___x_4976_, 2, v___x_4983_);
                    crate::leanh::lean_ctor_set(v___x_4976_, 0, v_fvarId_4981_);
                    v___x_4990_ = v___x_4976_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4994_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_fvarId_4981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4994_, 1, v_i_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4994_, 2, v___x_4983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4994_, 3, v_a_4985_);
                    v___x_4990_ = v_reuseFailAlloc_4994_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                if v_isShared_4988_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4987_, 0, v___x_4990_);
                    v___x_4992_ = v___x_4987_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4993_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 0, v___x_4990_);
                    v___x_4992_ = v_reuseFailAlloc_4993_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4992_;
            }
            49 => {
                v___x_5005_ = lean_st_ref_get(v_a_4752_);
                v___x_5006_ = 1;
                v___x_5007_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5005_,
                    v_fvarId_4998_,
                    v___x_5006_,
                );
                crate::leanh::lean_dec(v___x_5005_);
                if crate::leanh::lean_obj_tag(v___x_5007_) == 0 {
                    v_fvarId_5008_ = crate::leanh::lean_ctor_get(v___x_5007_, 0);
                    crate::leanh::lean_inc(v_fvarId_5008_);
                    crate::leanh::lean_dec_ref_known(v___x_5007_, 1);
                    v___x_5009_ = lean_st_ref_get(v_a_4752_);
                    v___x_5010_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_5009_,
                        v_y_5000_,
                        v___x_5006_,
                    );
                    crate::leanh::lean_dec(v___x_5009_);
                    if crate::leanh::lean_obj_tag(v___x_5010_) == 0 {
                        v_fvarId_5011_ = crate::leanh::lean_ctor_get(v___x_5010_, 0);
                        crate::leanh::lean_inc(v_fvarId_5011_);
                        crate::leanh::lean_dec_ref_known(v___x_5010_, 1);
                        v___x_5012_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                            v_pu_4749_, v_k_5001_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                            v_a_4755_, v_a_4756_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5012_) == 0 {
                            v_a_5013_ = crate::leanh::lean_ctor_get(v___x_5012_, 0);
                            v_isSharedCheck_5023_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5012_)) as u8;
                            if v_isSharedCheck_5023_ == 0 {
                                v___x_5015_ = v___x_5012_;
                                v_isShared_5016_ = v_isSharedCheck_5023_;
                                state = 50;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5013_);
                                crate::leanh::lean_dec(v___x_5012_);
                                v___x_5015_ = crate::leanh::lean_box(0);
                                v_isShared_5016_ = v_isSharedCheck_5023_;
                                state = 50;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_5011_);
                            crate::leanh::lean_dec(v_fvarId_5008_);
                            crate::leanh::lean_del_object(v___x_5003_);
                            crate::leanh::lean_dec(v_i_4999_);
                            return v___x_5012_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_5008_);
                        crate::leanh::lean_del_object(v___x_5003_);
                        crate::leanh::lean_dec_ref(v_k_5001_);
                        crate::leanh::lean_dec(v_i_4999_);
                        v___x_5024_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                        );
                        return v___x_5024_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5003_);
                    crate::leanh::lean_dec_ref(v_k_5001_);
                    crate::leanh::lean_dec(v_y_5000_);
                    crate::leanh::lean_dec(v_i_4999_);
                    v___x_5025_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_5025_;
                }
            }
            50 => {
                if v_isShared_5004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5003_, 3, v_a_5013_);
                    crate::leanh::lean_ctor_set(v___x_5003_, 2, v_fvarId_5011_);
                    crate::leanh::lean_ctor_set(v___x_5003_, 0, v_fvarId_5008_);
                    v___x_5018_ = v___x_5003_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_fvarId_5008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 1, v_i_4999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 2, v_fvarId_5011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 3, v_a_5013_);
                    v___x_5018_ = v_reuseFailAlloc_5022_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                if v_isShared_5016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5015_, 0, v___x_5018_);
                    v___x_5020_ = v___x_5015_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5021_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5018_);
                    v___x_5020_ = v_reuseFailAlloc_5021_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5020_;
            }
            53 => {
                v___x_5036_ = lean_st_ref_get(v_a_4752_);
                v___x_5037_ = 1;
                v___x_5038_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5036_,
                    v_fvarId_5027_,
                    v___x_5037_,
                );
                crate::leanh::lean_dec(v___x_5036_);
                if crate::leanh::lean_obj_tag(v___x_5038_) == 0 {
                    v_fvarId_5039_ = crate::leanh::lean_ctor_get(v___x_5038_, 0);
                    crate::leanh::lean_inc(v_fvarId_5039_);
                    crate::leanh::lean_dec_ref_known(v___x_5038_, 1);
                    v___x_5040_ = lean_st_ref_get(v_a_4752_);
                    v___x_5041_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_5040_,
                        v_y_5030_,
                        v___x_5037_,
                    );
                    crate::leanh::lean_dec(v___x_5040_);
                    if crate::leanh::lean_obj_tag(v___x_5041_) == 0 {
                        v_fvarId_5042_ = crate::leanh::lean_ctor_get(v___x_5041_, 0);
                        crate::leanh::lean_inc(v_fvarId_5042_);
                        crate::leanh::lean_dec_ref_known(v___x_5041_, 1);
                        v___x_5043_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_4749_, v_ty_5031_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
                        if crate::leanh::lean_obj_tag(v___x_5043_) == 0 {
                            v_a_5044_ = crate::leanh::lean_ctor_get(v___x_5043_, 0);
                            crate::leanh::lean_inc(v_a_5044_);
                            crate::leanh::lean_dec_ref_known(v___x_5043_, 1);
                            v___x_5045_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                                v_pu_4749_, v_k_5032_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                                v_a_4755_, v_a_4756_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5045_) == 0 {
                                v_a_5046_ = crate::leanh::lean_ctor_get(v___x_5045_, 0);
                                v_isSharedCheck_5056_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5045_)) as u8;
                                if v_isSharedCheck_5056_ == 0 {
                                    v___x_5048_ = v___x_5045_;
                                    v_isShared_5049_ = v_isSharedCheck_5056_;
                                    state = 54;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5046_);
                                    crate::leanh::lean_dec(v___x_5045_);
                                    v___x_5048_ = crate::leanh::lean_box(0);
                                    v_isShared_5049_ = v_isSharedCheck_5056_;
                                    state = 54;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5044_);
                                crate::leanh::lean_dec(v_fvarId_5042_);
                                crate::leanh::lean_dec(v_fvarId_5039_);
                                crate::leanh::lean_del_object(v___x_5034_);
                                crate::leanh::lean_dec(v_offset_5029_);
                                crate::leanh::lean_dec(v_i_5028_);
                                return v___x_5045_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_5042_);
                            crate::leanh::lean_dec(v_fvarId_5039_);
                            crate::leanh::lean_del_object(v___x_5034_);
                            crate::leanh::lean_dec_ref(v_k_5032_);
                            crate::leanh::lean_dec(v_offset_5029_);
                            crate::leanh::lean_dec(v_i_5028_);
                            v_a_5057_ = crate::leanh::lean_ctor_get(v___x_5043_, 0);
                            v_isSharedCheck_5064_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5043_)) as u8;
                            if v_isSharedCheck_5064_ == 0 {
                                v___x_5059_ = v___x_5043_;
                                v_isShared_5060_ = v_isSharedCheck_5064_;
                                state = 57;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5057_);
                                crate::leanh::lean_dec(v___x_5043_);
                                v___x_5059_ = crate::leanh::lean_box(0);
                                v_isShared_5060_ = v_isSharedCheck_5064_;
                                state = 57;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_5039_);
                        crate::leanh::lean_del_object(v___x_5034_);
                        crate::leanh::lean_dec_ref(v_k_5032_);
                        crate::leanh::lean_dec_ref(v_ty_5031_);
                        crate::leanh::lean_dec(v_offset_5029_);
                        crate::leanh::lean_dec(v_i_5028_);
                        v___x_5065_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                        );
                        return v___x_5065_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5034_);
                    crate::leanh::lean_dec_ref(v_k_5032_);
                    crate::leanh::lean_dec_ref(v_ty_5031_);
                    crate::leanh::lean_dec(v_y_5030_);
                    crate::leanh::lean_dec(v_offset_5029_);
                    crate::leanh::lean_dec(v_i_5028_);
                    v___x_5066_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_5066_;
                }
            }
            54 => {
                if v_isShared_5035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5034_, 5, v_a_5046_);
                    crate::leanh::lean_ctor_set(v___x_5034_, 4, v_a_5044_);
                    crate::leanh::lean_ctor_set(v___x_5034_, 3, v_fvarId_5042_);
                    crate::leanh::lean_ctor_set(v___x_5034_, 0, v_fvarId_5039_);
                    v___x_5051_ = v___x_5034_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_5055_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_fvarId_5039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 1, v_i_5028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 2, v_offset_5029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 3, v_fvarId_5042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 4, v_a_5044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 5, v_a_5046_);
                    v___x_5051_ = v_reuseFailAlloc_5055_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                if v_isShared_5049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5048_, 0, v___x_5051_);
                    v___x_5053_ = v___x_5048_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_5054_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5051_);
                    v___x_5053_ = v_reuseFailAlloc_5054_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_5053_;
            }
            57 => {
                if v_isShared_5060_ == 0 {
                    v___x_5062_ = v___x_5059_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_5063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
                    v___x_5062_ = v_reuseFailAlloc_5063_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_5062_;
            }
            59 => {
                v___x_5074_ = lean_st_ref_get(v_a_4752_);
                v___x_5075_ = 1;
                v___x_5076_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5074_,
                    v_fvarId_5068_,
                    v___x_5075_,
                );
                crate::leanh::lean_dec(v___x_5074_);
                if crate::leanh::lean_obj_tag(v___x_5076_) == 0 {
                    v_fvarId_5077_ = crate::leanh::lean_ctor_get(v___x_5076_, 0);
                    crate::leanh::lean_inc(v_fvarId_5077_);
                    crate::leanh::lean_dec_ref_known(v___x_5076_, 1);
                    v___x_5078_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                        v_pu_4749_, v_k_5070_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                        v_a_4755_, v_a_4756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5078_) == 0 {
                        v_a_5079_ = crate::leanh::lean_ctor_get(v___x_5078_, 0);
                        v_isSharedCheck_5089_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5078_)) as u8;
                        if v_isSharedCheck_5089_ == 0 {
                            v___x_5081_ = v___x_5078_;
                            v_isShared_5082_ = v_isSharedCheck_5089_;
                            state = 60;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5079_);
                            crate::leanh::lean_dec(v___x_5078_);
                            v___x_5081_ = crate::leanh::lean_box(0);
                            v_isShared_5082_ = v_isSharedCheck_5089_;
                            state = 60;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_5077_);
                        crate::leanh::lean_del_object(v___x_5072_);
                        crate::leanh::lean_dec(v_cidx_5069_);
                        return v___x_5078_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5072_);
                    crate::leanh::lean_dec_ref(v_k_5070_);
                    crate::leanh::lean_dec(v_cidx_5069_);
                    v___x_5090_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_5090_;
                }
            }
            60 => {
                if v_isShared_5073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5072_, 2, v_a_5079_);
                    crate::leanh::lean_ctor_set(v___x_5072_, 0, v_fvarId_5077_);
                    v___x_5084_ = v___x_5072_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_5088_ = crate::leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_fvarId_5077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 1, v_cidx_5069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 2, v_a_5079_);
                    v___x_5084_ = v_reuseFailAlloc_5088_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                if v_isShared_5082_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5081_, 0, v___x_5084_);
                    v___x_5086_ = v___x_5081_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_5087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5087_, 0, v___x_5084_);
                    v___x_5086_ = v_reuseFailAlloc_5087_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_5086_;
            }
            63 => {
                v___x_5100_ = lean_st_ref_get(v_a_4752_);
                v___x_5101_ = 1;
                v___x_5102_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5100_,
                    v_fvarId_5092_,
                    v___x_5101_,
                );
                crate::leanh::lean_dec(v___x_5100_);
                if crate::leanh::lean_obj_tag(v___x_5102_) == 0 {
                    v_fvarId_5103_ = crate::leanh::lean_ctor_get(v___x_5102_, 0);
                    crate::leanh::lean_inc(v_fvarId_5103_);
                    crate::leanh::lean_dec_ref_known(v___x_5102_, 1);
                    v___x_5104_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                        v_pu_4749_, v_k_5096_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                        v_a_4755_, v_a_4756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5104_) == 0 {
                        v_a_5105_ = crate::leanh::lean_ctor_get(v___x_5104_, 0);
                        v_isSharedCheck_5115_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5104_)) as u8;
                        if v_isSharedCheck_5115_ == 0 {
                            v___x_5107_ = v___x_5104_;
                            v_isShared_5108_ = v_isSharedCheck_5115_;
                            state = 64;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5105_);
                            crate::leanh::lean_dec(v___x_5104_);
                            v___x_5107_ = crate::leanh::lean_box(0);
                            v_isShared_5108_ = v_isSharedCheck_5115_;
                            state = 64;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_5103_);
                        crate::leanh::lean_del_object(v___x_5098_);
                        crate::leanh::lean_dec(v_n_5093_);
                        return v___x_5104_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5098_);
                    crate::leanh::lean_dec_ref(v_k_5096_);
                    crate::leanh::lean_dec(v_n_5093_);
                    v___x_5116_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_5116_;
                }
            }
            64 => {
                if v_isShared_5099_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5098_, 2, v_a_5105_);
                    crate::leanh::lean_ctor_set(v___x_5098_, 0, v_fvarId_5103_);
                    v___x_5110_ = v___x_5098_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_5114_ = crate::leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_fvarId_5103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5114_, 1, v_n_5093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5114_, 2, v_a_5105_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5114_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_check_5094_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5114_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_5095_,
                    );
                    v___x_5110_ = v_reuseFailAlloc_5114_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                if v_isShared_5108_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5107_, 0, v___x_5110_);
                    v___x_5112_ = v___x_5107_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_5113_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5110_);
                    v___x_5112_ = v_reuseFailAlloc_5113_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_5112_;
            }
            67 => {
                v___x_5127_ = lean_st_ref_get(v_a_4752_);
                v___x_5128_ = 1;
                v___x_5129_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5127_,
                    v_fvarId_5118_,
                    v___x_5128_,
                );
                crate::leanh::lean_dec(v___x_5127_);
                if crate::leanh::lean_obj_tag(v___x_5129_) == 0 {
                    v_fvarId_5130_ = crate::leanh::lean_ctor_get(v___x_5129_, 0);
                    crate::leanh::lean_inc(v_fvarId_5130_);
                    crate::leanh::lean_dec_ref_known(v___x_5129_, 1);
                    v___x_5131_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                        v_pu_4749_, v_k_5123_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                        v_a_4755_, v_a_4756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5131_) == 0 {
                        v_a_5132_ = crate::leanh::lean_ctor_get(v___x_5131_, 0);
                        v_isSharedCheck_5142_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5131_)) as u8;
                        if v_isSharedCheck_5142_ == 0 {
                            v___x_5134_ = v___x_5131_;
                            v_isShared_5135_ = v_isSharedCheck_5142_;
                            state = 68;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5132_);
                            crate::leanh::lean_dec(v___x_5131_);
                            v___x_5134_ = crate::leanh::lean_box(0);
                            v_isShared_5135_ = v_isSharedCheck_5142_;
                            state = 68;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_5130_);
                        crate::leanh::lean_del_object(v___x_5125_);
                        crate::leanh::lean_dec(v_objs_x3f_5122_);
                        crate::leanh::lean_dec(v_n_5119_);
                        return v___x_5131_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5125_);
                    crate::leanh::lean_dec_ref(v_k_5123_);
                    crate::leanh::lean_dec(v_objs_x3f_5122_);
                    crate::leanh::lean_dec(v_n_5119_);
                    v___x_5143_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_5143_;
                }
            }
            68 => {
                if v_isShared_5126_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5125_, 3, v_a_5132_);
                    crate::leanh::lean_ctor_set(v___x_5125_, 0, v_fvarId_5130_);
                    v___x_5137_ = v___x_5125_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_5141_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_fvarId_5130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 1, v_n_5119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 2, v_objs_x3f_5122_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 3, v_a_5132_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5141_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_check_5120_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5141_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_5121_,
                    );
                    v___x_5137_ = v_reuseFailAlloc_5141_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_5135_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5134_, 0, v___x_5137_);
                    v___x_5139_ = v___x_5134_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_5140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5140_, 0, v___x_5137_);
                    v___x_5139_ = v_reuseFailAlloc_5140_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_5139_;
            }
            71 => {
                v___x_5150_ = lean_st_ref_get(v_a_4752_);
                v___x_5151_ = 1;
                v___x_5152_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5150_,
                    v_fvarId_5145_,
                    v___x_5151_,
                );
                crate::leanh::lean_dec(v___x_5150_);
                if crate::leanh::lean_obj_tag(v___x_5152_) == 0 {
                    v_fvarId_5153_ = crate::leanh::lean_ctor_get(v___x_5152_, 0);
                    crate::leanh::lean_inc(v_fvarId_5153_);
                    crate::leanh::lean_dec_ref_known(v___x_5152_, 1);
                    v___x_5154_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                        v_pu_4749_, v_k_5146_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_,
                        v_a_4755_, v_a_4756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5154_) == 0 {
                        v_a_5155_ = crate::leanh::lean_ctor_get(v___x_5154_, 0);
                        v_isSharedCheck_5165_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5154_)) as u8;
                        if v_isSharedCheck_5165_ == 0 {
                            v___x_5157_ = v___x_5154_;
                            v_isShared_5158_ = v_isSharedCheck_5165_;
                            state = 72;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5155_);
                            crate::leanh::lean_dec(v___x_5154_);
                            v___x_5157_ = crate::leanh::lean_box(0);
                            v_isShared_5158_ = v_isSharedCheck_5165_;
                            state = 72;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_5153_);
                        crate::leanh::lean_del_object(v___x_5148_);
                        return v___x_5154_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5148_);
                    crate::leanh::lean_dec_ref(v_k_5146_);
                    v___x_5166_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_4749_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_,
                    );
                    return v___x_5166_;
                }
            }
            72 => {
                if v_isShared_5149_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5148_, 1, v_a_5155_);
                    crate::leanh::lean_ctor_set(v___x_5148_, 0, v_fvarId_5153_);
                    v___x_5160_ = v___x_5148_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_5164_ = crate::leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_fvarId_5153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5164_, 1, v_a_5155_);
                    v___x_5160_ = v_reuseFailAlloc_5164_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                if v_isShared_5158_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5157_, 0, v___x_5160_);
                    v___x_5162_ = v___x_5157_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_5163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 0, v___x_5160_);
                    v___x_5162_ = v_reuseFailAlloc_5163_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                return v___x_5162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(
    mut v_pu_5168_: u8,
    mut v_decl_5169_: *mut crate::leanh::LeanObject,
    mut v_a_5170_: u8,
    mut v_a_5171_: *mut crate::leanh::LeanObject,
    mut v_a_5172_: *mut crate::leanh::LeanObject,
    mut v_a_5173_: *mut crate::leanh::LeanObject,
    mut v_a_5174_: *mut crate::leanh::LeanObject,
    mut v_a_5175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5189_: usize = 0;
    let mut v___x_5190_: usize = 0;
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5199_: u8 = 0;
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5205_: u8 = 0;
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5217_: u8 = 0;
    let mut v_isSharedCheck_5218_: u8 = 0;
    let mut v_a_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5222_: u8 = 0;
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5226_: u8 = 0;
    let mut v_a_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5230_: u8 = 0;
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5234_: u8 = 0;
    let mut v_a_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5242_: u8 = 0;
    let mut v_a_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5246_: u8 = 0;
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5250_: u8 = 0;
    let mut v_a_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5254_: u8 = 0;
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5258_: u8 = 0;
    let mut v_isSharedCheck_5259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_5177_ = crate::leanh::lean_ctor_get(v_decl_5169_, 0);
                v_binderName_5178_ = crate::leanh::lean_ctor_get(v_decl_5169_, 1);
                v_params_5179_ = crate::leanh::lean_ctor_get(v_decl_5169_, 2);
                v_type_5180_ = crate::leanh::lean_ctor_get(v_decl_5169_, 3);
                v_value_5181_ = crate::leanh::lean_ctor_get(v_decl_5169_, 4);
                v_isSharedCheck_5259_ = (!crate::leanh::lean_is_exclusive(v_decl_5169_)) as u8;
                if v_isSharedCheck_5259_ == 0 {
                    v___x_5183_ = v_decl_5169_;
                    v_isShared_5184_ = v_isSharedCheck_5259_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_value_5181_);
                    crate::leanh::lean_inc(v_type_5180_);
                    crate::leanh::lean_inc(v_params_5179_);
                    crate::leanh::lean_inc(v_binderName_5178_);
                    crate::leanh::lean_inc(v_fvarId_5177_);
                    crate::leanh::lean_dec(v_decl_5169_);
                    v___x_5183_ = crate::leanh::lean_box(0);
                    v_isShared_5184_ = v_isSharedCheck_5259_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5185_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_5168_, v_type_5180_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
                if crate::leanh::lean_obj_tag(v___x_5185_) == 0 {
                    v_a_5186_ = crate::leanh::lean_ctor_get(v___x_5185_, 0);
                    crate::leanh::lean_inc(v_a_5186_);
                    crate::leanh::lean_dec_ref_known(v___x_5185_, 1);
                    v___x_5187_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(v_binderName_5178_, v_a_5170_, v_a_5173_);
                    if crate::leanh::lean_obj_tag(v___x_5187_) == 0 {
                        v_a_5188_ = crate::leanh::lean_ctor_get(v___x_5187_, 0);
                        crate::leanh::lean_inc(v_a_5188_);
                        crate::leanh::lean_dec_ref_known(v___x_5187_, 1);
                        v_sz_5189_ = lean_array_size(v_params_5179_);
                        v___x_5190_ = 0usize;
                        v___x_5191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_5168_, v_sz_5189_, v___x_5190_, v_params_5179_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
                        if crate::leanh::lean_obj_tag(v___x_5191_) == 0 {
                            v_a_5192_ = crate::leanh::lean_ctor_get(v___x_5191_, 0);
                            crate::leanh::lean_inc(v_a_5192_);
                            crate::leanh::lean_dec_ref_known(v___x_5191_, 1);
                            v___x_5193_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                                v_pu_5168_,
                                v_value_5181_,
                                v_a_5170_,
                                v_a_5171_,
                                v_a_5172_,
                                v_a_5173_,
                                v_a_5174_,
                                v_a_5175_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5193_) == 0 {
                                v_a_5194_ = crate::leanh::lean_ctor_get(v___x_5193_, 0);
                                crate::leanh::lean_inc(v_a_5194_);
                                crate::leanh::lean_dec_ref_known(v___x_5193_, 1);
                                v___x_5195_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(v_fvarId_5177_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
                                if crate::leanh::lean_obj_tag(v___x_5195_) == 0 {
                                    v_a_5196_ = crate::leanh::lean_ctor_get(v___x_5195_, 0);
                                    v_isSharedCheck_5218_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5195_)) as u8;
                                    if v_isSharedCheck_5218_ == 0 {
                                        v___x_5198_ = v___x_5195_;
                                        v_isShared_5199_ = v_isSharedCheck_5218_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5196_);
                                        crate::leanh::lean_dec(v___x_5195_);
                                        v___x_5198_ = crate::leanh::lean_box(0);
                                        v_isShared_5199_ = v_isSharedCheck_5218_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5194_);
                                    crate::leanh::lean_dec(v_a_5192_);
                                    crate::leanh::lean_dec(v_a_5188_);
                                    crate::leanh::lean_dec(v_a_5186_);
                                    crate::leanh::lean_del_object(v___x_5183_);
                                    v_a_5219_ = crate::leanh::lean_ctor_get(v___x_5195_, 0);
                                    v_isSharedCheck_5226_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5195_)) as u8;
                                    if v_isSharedCheck_5226_ == 0 {
                                        v___x_5221_ = v___x_5195_;
                                        v_isShared_5222_ = v_isSharedCheck_5226_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5219_);
                                        crate::leanh::lean_dec(v___x_5195_);
                                        v___x_5221_ = crate::leanh::lean_box(0);
                                        v_isShared_5222_ = v_isSharedCheck_5226_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5192_);
                                crate::leanh::lean_dec(v_a_5188_);
                                crate::leanh::lean_dec(v_a_5186_);
                                crate::leanh::lean_del_object(v___x_5183_);
                                crate::leanh::lean_dec(v_fvarId_5177_);
                                v_a_5227_ = crate::leanh::lean_ctor_get(v___x_5193_, 0);
                                v_isSharedCheck_5234_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5193_)) as u8;
                                if v_isSharedCheck_5234_ == 0 {
                                    v___x_5229_ = v___x_5193_;
                                    v_isShared_5230_ = v_isSharedCheck_5234_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5227_);
                                    crate::leanh::lean_dec(v___x_5193_);
                                    v___x_5229_ = crate::leanh::lean_box(0);
                                    v_isShared_5230_ = v_isSharedCheck_5234_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5188_);
                            crate::leanh::lean_dec(v_a_5186_);
                            crate::leanh::lean_del_object(v___x_5183_);
                            crate::leanh::lean_dec_ref(v_value_5181_);
                            crate::leanh::lean_dec(v_fvarId_5177_);
                            v_a_5235_ = crate::leanh::lean_ctor_get(v___x_5191_, 0);
                            v_isSharedCheck_5242_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5191_)) as u8;
                            if v_isSharedCheck_5242_ == 0 {
                                v___x_5237_ = v___x_5191_;
                                v_isShared_5238_ = v_isSharedCheck_5242_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5235_);
                                crate::leanh::lean_dec(v___x_5191_);
                                v___x_5237_ = crate::leanh::lean_box(0);
                                v_isShared_5238_ = v_isSharedCheck_5242_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5186_);
                        crate::leanh::lean_del_object(v___x_5183_);
                        crate::leanh::lean_dec_ref(v_value_5181_);
                        crate::leanh::lean_dec_ref(v_params_5179_);
                        crate::leanh::lean_dec(v_fvarId_5177_);
                        v_a_5243_ = crate::leanh::lean_ctor_get(v___x_5187_, 0);
                        v_isSharedCheck_5250_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5187_)) as u8;
                        if v_isSharedCheck_5250_ == 0 {
                            v___x_5245_ = v___x_5187_;
                            v_isShared_5246_ = v_isSharedCheck_5250_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5243_);
                            crate::leanh::lean_dec(v___x_5187_);
                            v___x_5245_ = crate::leanh::lean_box(0);
                            v_isShared_5246_ = v_isSharedCheck_5250_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5183_);
                    crate::leanh::lean_dec_ref(v_value_5181_);
                    crate::leanh::lean_dec_ref(v_params_5179_);
                    crate::leanh::lean_dec(v_binderName_5178_);
                    crate::leanh::lean_dec(v_fvarId_5177_);
                    v_a_5251_ = crate::leanh::lean_ctor_get(v___x_5185_, 0);
                    v_isSharedCheck_5258_ = (!crate::leanh::lean_is_exclusive(v___x_5185_)) as u8;
                    if v_isSharedCheck_5258_ == 0 {
                        v___x_5253_ = v___x_5185_;
                        v_isShared_5254_ = v_isSharedCheck_5258_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5251_);
                        crate::leanh::lean_dec(v___x_5185_);
                        v___x_5253_ = crate::leanh::lean_box(0);
                        v_isShared_5254_ = v_isSharedCheck_5258_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5200_ = lean_st_ref_take(v_a_5173_);
                v_lctx_5201_ = crate::leanh::lean_ctor_get(v___x_5200_, 0);
                v_nextIdx_5202_ = crate::leanh::lean_ctor_get(v___x_5200_, 1);
                v_isSharedCheck_5217_ = (!crate::leanh::lean_is_exclusive(v___x_5200_)) as u8;
                if v_isSharedCheck_5217_ == 0 {
                    v___x_5204_ = v___x_5200_;
                    v_isShared_5205_ = v_isSharedCheck_5217_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_5202_);
                    crate::leanh::lean_inc(v_lctx_5201_);
                    crate::leanh::lean_dec(v___x_5200_);
                    v___x_5204_ = crate::leanh::lean_box(0);
                    v_isShared_5205_ = v_isSharedCheck_5217_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5183_, 4, v_a_5194_);
                    crate::leanh::lean_ctor_set(v___x_5183_, 3, v_a_5186_);
                    crate::leanh::lean_ctor_set(v___x_5183_, 2, v_a_5192_);
                    crate::leanh::lean_ctor_set(v___x_5183_, 1, v_a_5188_);
                    crate::leanh::lean_ctor_set(v___x_5183_, 0, v_a_5196_);
                    v___x_5207_ = v___x_5183_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5216_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 1, v_a_5188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 2, v_a_5192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 3, v_a_5186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 4, v_a_5194_);
                    v___x_5207_ = v_reuseFailAlloc_5216_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_5207_);
                v___x_5208_ =
                    l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_5168_, v_lctx_5201_, v___x_5207_);
                if v_isShared_5205_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5204_, 0, v___x_5208_);
                    v___x_5210_ = v___x_5204_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5215_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5215_, 0, v___x_5208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5215_, 1, v_nextIdx_5202_);
                    v___x_5210_ = v_reuseFailAlloc_5215_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5211_ = lean_st_ref_set(v_a_5173_, v___x_5210_);
                if v_isShared_5199_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5198_, 0, v___x_5207_);
                    v___x_5213_ = v___x_5198_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 0, v___x_5207_);
                    v___x_5213_ = v_reuseFailAlloc_5214_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5213_;
            }
            7 => {
                if v_isShared_5222_ == 0 {
                    v___x_5224_ = v___x_5221_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5225_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_a_5219_);
                    v___x_5224_ = v_reuseFailAlloc_5225_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5224_;
            }
            9 => {
                if v_isShared_5230_ == 0 {
                    v___x_5232_ = v___x_5229_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_a_5227_);
                    v___x_5232_ = v_reuseFailAlloc_5233_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5232_;
            }
            11 => {
                if v_isShared_5238_ == 0 {
                    v___x_5240_ = v___x_5237_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5241_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
                    v___x_5240_ = v_reuseFailAlloc_5241_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5240_;
            }
            13 => {
                if v_isShared_5246_ == 0 {
                    v___x_5248_ = v___x_5245_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5249_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_a_5243_);
                    v___x_5248_ = v_reuseFailAlloc_5249_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5248_;
            }
            15 => {
                if v_isShared_5254_ == 0 {
                    v___x_5256_ = v___x_5253_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5257_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_a_5251_);
                    v___x_5256_ = v_reuseFailAlloc_5257_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(
    mut v_pu_5260_: *mut crate::leanh::LeanObject,
    mut v_decl_5261_: *mut crate::leanh::LeanObject,
    mut v_a_5262_: *mut crate::leanh::LeanObject,
    mut v_a_5263_: *mut crate::leanh::LeanObject,
    mut v_a_5264_: *mut crate::leanh::LeanObject,
    mut v_a_5265_: *mut crate::leanh::LeanObject,
    mut v_a_5266_: *mut crate::leanh::LeanObject,
    mut v_a_5267_: *mut crate::leanh::LeanObject,
    mut v_a_5268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5269_: u8 = 0;
    let mut v_a_boxed_5270_: u8 = 0;
    let mut v_res_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5269_ = (crate::leanh::lean_unbox(v_pu_5260_) as u8);
    v_a_boxed_5270_ = (crate::leanh::lean_unbox(v_a_5262_) as u8);
    v_res_5271_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(
        v_pu_boxed_5269_,
        v_decl_5261_,
        v_a_boxed_5270_,
        v_a_5263_,
        v_a_5264_,
        v_a_5265_,
        v_a_5266_,
        v_a_5267_,
    );
    crate::leanh::lean_dec(v_a_5267_);
    crate::leanh::lean_dec_ref(v_a_5266_);
    crate::leanh::lean_dec(v_a_5265_);
    crate::leanh::lean_dec_ref(v_a_5264_);
    crate::leanh::lean_dec(v_a_5263_);
    return v_res_5271_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(
    mut v_pu_5272_: *mut crate::leanh::LeanObject,
    mut v_sz_5273_: *mut crate::leanh::LeanObject,
    mut v_i_5274_: *mut crate::leanh::LeanObject,
    mut v_bs_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
    mut v___y_5281_: *mut crate::leanh::LeanObject,
    mut v___y_5282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5283_: u8 = 0;
    let mut v_sz_boxed_5284_: usize = 0;
    let mut v_i_boxed_5285_: usize = 0;
    let mut v___y_26956__boxed_5286_: u8 = 0;
    let mut v_res_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5283_ = (crate::leanh::lean_unbox(v_pu_5272_) as u8);
    v_sz_boxed_5284_ = crate::leanh::lean_unbox_usize(v_sz_5273_);
    crate::leanh::lean_dec(v_sz_5273_);
    v_i_boxed_5285_ = crate::leanh::lean_unbox_usize(v_i_5274_);
    crate::leanh::lean_dec(v_i_5274_);
    v___y_26956__boxed_5286_ = (crate::leanh::lean_unbox(v___y_5276_) as u8);
    v_res_5287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(v_pu_boxed_5283_, v_sz_boxed_5284_, v_i_boxed_5285_, v_bs_5275_, v___y_26956__boxed_5286_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_);
    crate::leanh::lean_dec(v___y_5281_);
    crate::leanh::lean_dec_ref(v___y_5280_);
    crate::leanh::lean_dec(v___y_5279_);
    crate::leanh::lean_dec_ref(v___y_5278_);
    crate::leanh::lean_dec(v___y_5277_);
    return v_res_5287_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(
    mut v_pu_5288_: *mut crate::leanh::LeanObject,
    mut v_code_5289_: *mut crate::leanh::LeanObject,
    mut v_a_5290_: *mut crate::leanh::LeanObject,
    mut v_a_5291_: *mut crate::leanh::LeanObject,
    mut v_a_5292_: *mut crate::leanh::LeanObject,
    mut v_a_5293_: *mut crate::leanh::LeanObject,
    mut v_a_5294_: *mut crate::leanh::LeanObject,
    mut v_a_5295_: *mut crate::leanh::LeanObject,
    mut v_a_5296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5297_: u8 = 0;
    let mut v_a_boxed_5298_: u8 = 0;
    let mut v_res_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5297_ = (crate::leanh::lean_unbox(v_pu_5288_) as u8);
    v_a_boxed_5298_ = (crate::leanh::lean_unbox(v_a_5290_) as u8);
    v_res_5299_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
        v_pu_boxed_5297_,
        v_code_5289_,
        v_a_boxed_5298_,
        v_a_5291_,
        v_a_5292_,
        v_a_5293_,
        v_a_5294_,
        v_a_5295_,
    );
    crate::leanh::lean_dec(v_a_5295_);
    crate::leanh::lean_dec_ref(v_a_5294_);
    crate::leanh::lean_dec(v_a_5293_);
    crate::leanh::lean_dec_ref(v_a_5292_);
    crate::leanh::lean_dec(v_a_5291_);
    return v_res_5299_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(
    mut v_pu_5300_: u8,
    mut v_msg_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: u8,
    mut v___y_5303_: *mut crate::leanh::LeanObject,
    mut v___y_5304_: *mut crate::leanh::LeanObject,
    mut v___y_5305_: *mut crate::leanh::LeanObject,
    mut v___y_5306_: *mut crate::leanh::LeanObject,
    mut v___y_5307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5314_: u8 = 0;
    let mut v_toFunctor_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5321_: u8 = 0;
    let mut v___f_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5338_: u8 = 0;
    let mut v_toFunctor_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5345_: u8 = 0;
    let mut v___f_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11427__overap_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5367_: u8 = 0;
    let mut v_unused_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5369_: u8 = 0;
    let mut v_unused_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5373_: u8 = 0;
    let mut v_unused_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut v_unused_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5309_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
                v___x_5310_ = l_StateRefT_x27_instMonad___redArg(v___x_5309_);
                v_toApplicative_5311_ = crate::leanh::lean_ctor_get(v___x_5310_, 0);
                v_isSharedCheck_5375_ = (!crate::leanh::lean_is_exclusive(v___x_5310_)) as u8;
                if v_isSharedCheck_5375_ == 0 {
                    v_unused_5376_ = crate::leanh::lean_ctor_get(v___x_5310_, 1);
                    crate::leanh::lean_dec(v_unused_5376_);
                    v___x_5313_ = v___x_5310_;
                    v_isShared_5314_ = v_isSharedCheck_5375_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5311_);
                    crate::leanh::lean_dec(v___x_5310_);
                    v___x_5313_ = crate::leanh::lean_box(0);
                    v_isShared_5314_ = v_isSharedCheck_5375_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5315_ = crate::leanh::lean_ctor_get(v_toApplicative_5311_, 0);
                v_toSeq_5316_ = crate::leanh::lean_ctor_get(v_toApplicative_5311_, 2);
                v_toSeqLeft_5317_ = crate::leanh::lean_ctor_get(v_toApplicative_5311_, 3);
                v_toSeqRight_5318_ = crate::leanh::lean_ctor_get(v_toApplicative_5311_, 4);
                v_isSharedCheck_5373_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5311_)) as u8;
                if v_isSharedCheck_5373_ == 0 {
                    v_unused_5374_ = crate::leanh::lean_ctor_get(v_toApplicative_5311_, 1);
                    crate::leanh::lean_dec(v_unused_5374_);
                    v___x_5320_ = v_toApplicative_5311_;
                    v_isShared_5321_ = v_isSharedCheck_5373_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5318_);
                    crate::leanh::lean_inc(v_toSeqLeft_5317_);
                    crate::leanh::lean_inc(v_toSeq_5316_);
                    crate::leanh::lean_inc(v_toFunctor_5315_);
                    crate::leanh::lean_dec(v_toApplicative_5311_);
                    v___x_5320_ = crate::leanh::lean_box(0);
                    v_isShared_5321_ = v_isSharedCheck_5373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5322_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1;
                v___f_5323_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_5315_);
                v___f_5324_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5324_, 0, v_toFunctor_5315_);
                v___f_5325_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5325_, 0, v_toFunctor_5315_);
                v___x_5326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5326_, 0, v___f_5324_);
                crate::leanh::lean_ctor_set(v___x_5326_, 1, v___f_5325_);
                v___f_5327_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5327_, 0, v_toSeqRight_5318_);
                v___f_5328_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5328_, 0, v_toSeqLeft_5317_);
                v___f_5329_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5329_, 0, v_toSeq_5316_);
                if v_isShared_5321_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5320_, 4, v___f_5327_);
                    crate::leanh::lean_ctor_set(v___x_5320_, 3, v___f_5328_);
                    crate::leanh::lean_ctor_set(v___x_5320_, 2, v___f_5329_);
                    crate::leanh::lean_ctor_set(v___x_5320_, 1, v___f_5322_);
                    crate::leanh::lean_ctor_set(v___x_5320_, 0, v___x_5326_);
                    v___x_5331_ = v___x_5320_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5372_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 1, v___f_5322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 2, v___f_5329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 3, v___f_5328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 4, v___f_5327_);
                    v___x_5331_ = v_reuseFailAlloc_5372_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5314_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5313_, 1, v___f_5323_);
                    crate::leanh::lean_ctor_set(v___x_5313_, 0, v___x_5331_);
                    v___x_5333_ = v___x_5313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 1, v___f_5323_);
                    v___x_5333_ = v_reuseFailAlloc_5371_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5334_ = l_StateRefT_x27_instMonad___redArg(v___x_5333_);
                v_toApplicative_5335_ = crate::leanh::lean_ctor_get(v___x_5334_, 0);
                v_isSharedCheck_5369_ = (!crate::leanh::lean_is_exclusive(v___x_5334_)) as u8;
                if v_isSharedCheck_5369_ == 0 {
                    v_unused_5370_ = crate::leanh::lean_ctor_get(v___x_5334_, 1);
                    crate::leanh::lean_dec(v_unused_5370_);
                    v___x_5337_ = v___x_5334_;
                    v_isShared_5338_ = v_isSharedCheck_5369_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5335_);
                    crate::leanh::lean_dec(v___x_5334_);
                    v___x_5337_ = crate::leanh::lean_box(0);
                    v_isShared_5338_ = v_isSharedCheck_5369_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_5339_ = crate::leanh::lean_ctor_get(v_toApplicative_5335_, 0);
                v_toSeq_5340_ = crate::leanh::lean_ctor_get(v_toApplicative_5335_, 2);
                v_toSeqLeft_5341_ = crate::leanh::lean_ctor_get(v_toApplicative_5335_, 3);
                v_toSeqRight_5342_ = crate::leanh::lean_ctor_get(v_toApplicative_5335_, 4);
                v_isSharedCheck_5367_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5335_)) as u8;
                if v_isSharedCheck_5367_ == 0 {
                    v_unused_5368_ = crate::leanh::lean_ctor_get(v_toApplicative_5335_, 1);
                    crate::leanh::lean_dec(v_unused_5368_);
                    v___x_5344_ = v_toApplicative_5335_;
                    v_isShared_5345_ = v_isSharedCheck_5367_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5342_);
                    crate::leanh::lean_inc(v_toSeqLeft_5341_);
                    crate::leanh::lean_inc(v_toSeq_5340_);
                    crate::leanh::lean_inc(v_toFunctor_5339_);
                    crate::leanh::lean_dec(v_toApplicative_5335_);
                    v___x_5344_ = crate::leanh::lean_box(0);
                    v_isShared_5345_ = v_isSharedCheck_5367_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_5346_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3;
                v___f_5347_ = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_5339_);
                v___f_5348_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5348_, 0, v_toFunctor_5339_);
                v___f_5349_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5349_, 0, v_toFunctor_5339_);
                v___x_5350_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5350_, 0, v___f_5348_);
                crate::leanh::lean_ctor_set(v___x_5350_, 1, v___f_5349_);
                v___f_5351_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5351_, 0, v_toSeqRight_5342_);
                v___f_5352_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5352_, 0, v_toSeqLeft_5341_);
                v___f_5353_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5353_, 0, v_toSeq_5340_);
                if v_isShared_5345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5344_, 4, v___f_5351_);
                    crate::leanh::lean_ctor_set(v___x_5344_, 3, v___f_5352_);
                    crate::leanh::lean_ctor_set(v___x_5344_, 2, v___f_5353_);
                    crate::leanh::lean_ctor_set(v___x_5344_, 1, v___f_5346_);
                    crate::leanh::lean_ctor_set(v___x_5344_, 0, v___x_5350_);
                    v___x_5355_ = v___x_5344_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5366_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 0, v___x_5350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 1, v___f_5346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 2, v___f_5353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 3, v___f_5352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 4, v___f_5351_);
                    v___x_5355_ = v_reuseFailAlloc_5366_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5337_, 1, v___f_5347_);
                    crate::leanh::lean_ctor_set(v___x_5337_, 0, v___x_5355_);
                    v___x_5357_ = v___x_5337_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5365_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 0, v___x_5355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 1, v___f_5347_);
                    v___x_5357_ = v_reuseFailAlloc_5365_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5358_ = l_StateRefT_x27_instMonad___redArg(v___x_5357_);
                v___x_5359_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v_pu_5300_);
                v___x_5360_ = l_instInhabitedOfMonad___redArg(v___x_5358_, v___x_5359_);
                v___f_5361_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5361_, 0, v___x_5360_);
                v___x_11427__overap_5362_ = lean_panic_fn_borrowed(v___f_5361_, v_msg_5301_);
                crate::leanh::lean_dec_ref(v___f_5361_);
                v___x_5363_ = crate::leanh::lean_box((v___y_5302_) as usize);
                crate::leanh::lean_inc(v___y_5307_);
                crate::leanh::lean_inc_ref(v___y_5306_);
                crate::leanh::lean_inc(v___y_5305_);
                crate::leanh::lean_inc_ref(v___y_5304_);
                crate::leanh::lean_inc(v___y_5303_);
                v___x_5364_ = crate::leanh::lean_apply_7(
                    v___x_11427__overap_5362_,
                    v___x_5363_,
                    v___y_5303_,
                    v___y_5304_,
                    v___y_5305_,
                    v___y_5306_,
                    v___y_5307_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(
    mut v_pu_5377_: *mut crate::leanh::LeanObject,
    mut v_msg_5378_: *mut crate::leanh::LeanObject,
    mut v___y_5379_: *mut crate::leanh::LeanObject,
    mut v___y_5380_: *mut crate::leanh::LeanObject,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
    mut v___y_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5386_: u8 = 0;
    let mut v___y_11458__boxed_5387_: u8 = 0;
    let mut v_res_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5386_ = (crate::leanh::lean_unbox(v_pu_5377_) as u8);
    v___y_11458__boxed_5387_ = (crate::leanh::lean_unbox(v___y_5379_) as u8);
    v_res_5388_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(
        v_pu_boxed_5386_,
        v_msg_5378_,
        v___y_11458__boxed_5387_,
        v___y_5380_,
        v___y_5381_,
        v___y_5382_,
        v___y_5383_,
        v___y_5384_,
    );
    crate::leanh::lean_dec(v___y_5384_);
    crate::leanh::lean_dec_ref(v___y_5383_);
    crate::leanh::lean_dec(v___y_5382_);
    crate::leanh::lean_dec_ref(v___y_5381_);
    crate::leanh::lean_dec(v___y_5380_);
    return v_res_5388_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5390_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_5391_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_5392_ = crate::leanh::lean_unsigned_to_nat(217);
    v___x_5393_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0;
    v___x_5394_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_5395_ = l_mkPanicMessageWithDecl(
        v___x_5394_,
        v___x_5393_,
        v___x_5392_,
        v___x_5391_,
        v___x_5390_,
    );
    return v___x_5395_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5396_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_5397_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_5398_ = crate::leanh::lean_unsigned_to_nat(222);
    v___x_5399_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0;
    v___x_5400_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_5401_ = l_mkPanicMessageWithDecl(
        v___x_5400_,
        v___x_5399_,
        v___x_5398_,
        v___x_5397_,
        v___x_5396_,
    );
    return v___x_5401_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5402_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_5403_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_5404_ = crate::leanh::lean_unsigned_to_nat(221);
    v___x_5405_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0;
    v___x_5406_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_5407_ = l_mkPanicMessageWithDecl(
        v___x_5406_,
        v___x_5405_,
        v___x_5404_,
        v___x_5403_,
        v___x_5402_,
    );
    return v___x_5407_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5408_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_5409_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_5410_ = crate::leanh::lean_unsigned_to_nat(226);
    v___x_5411_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0;
    v___x_5412_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_5413_ = l_mkPanicMessageWithDecl(
        v___x_5412_,
        v___x_5411_,
        v___x_5410_,
        v___x_5409_,
        v___x_5408_,
    );
    return v___x_5413_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5414_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_5415_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_5416_ = crate::leanh::lean_unsigned_to_nat(225);
    v___x_5417_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0;
    v___x_5418_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_5419_ = l_mkPanicMessageWithDecl(
        v___x_5418_,
        v___x_5417_,
        v___x_5416_,
        v___x_5415_,
        v___x_5414_,
    );
    return v___x_5419_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5420_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_5421_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_5422_ = crate::leanh::lean_unsigned_to_nat(230);
    v___x_5423_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0;
    v___x_5424_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_5425_ = l_mkPanicMessageWithDecl(
        v___x_5424_,
        v___x_5423_,
        v___x_5422_,
        v___x_5421_,
        v___x_5420_,
    );
    return v___x_5425_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5426_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_5427_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_5428_ = crate::leanh::lean_unsigned_to_nat(233);
    v___x_5429_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0;
    v___x_5430_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_5431_ = l_mkPanicMessageWithDecl(
        v___x_5430_,
        v___x_5429_,
        v___x_5428_,
        v___x_5427_,
        v___x_5426_,
    );
    return v___x_5431_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5432_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_5433_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_5434_ = crate::leanh::lean_unsigned_to_nat(236);
    v___x_5435_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0;
    v___x_5436_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_5437_ = l_mkPanicMessageWithDecl(
        v___x_5436_,
        v___x_5435_,
        v___x_5434_,
        v___x_5433_,
        v___x_5432_,
    );
    return v___x_5437_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5438_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2;
    v___x_5439_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_5440_ = crate::leanh::lean_unsigned_to_nat(239);
    v___x_5441_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0;
    v___x_5442_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0;
    v___x_5443_ = l_mkPanicMessageWithDecl(
        v___x_5442_,
        v___x_5441_,
        v___x_5440_,
        v___x_5439_,
        v___x_5438_,
    );
    return v___x_5443_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(
    mut v_pu_5444_: u8,
    mut v_decl_5445_: *mut crate::leanh::LeanObject,
    mut v_a_5446_: u8,
    mut v_a_5447_: *mut crate::leanh::LeanObject,
    mut v_a_5448_: *mut crate::leanh::LeanObject,
    mut v_a_5449_: *mut crate::leanh::LeanObject,
    mut v_a_5450_: *mut crate::leanh::LeanObject,
    mut v_a_5451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5456_: u8 = 0;
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5461_: u8 = 0;
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5468_: u8 = 0;
    let mut v_a_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5472_: u8 = 0;
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5476_: u8 = 0;
    let mut v_isSharedCheck_5477_: u8 = 0;
    let mut v_decl_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5481_: u8 = 0;
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5486_: u8 = 0;
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5493_: u8 = 0;
    let mut v_a_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5497_: u8 = 0;
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5501_: u8 = 0;
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut v_decl_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5506_: u8 = 0;
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5511_: u8 = 0;
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5518_: u8 = 0;
    let mut v_a_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5522_: u8 = 0;
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5526_: u8 = 0;
    let mut v_isSharedCheck_5527_: u8 = 0;
    let mut v_fvarId_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5533_: u8 = 0;
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: u8 = 0;
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5540_: u8 = 0;
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5549_: u8 = 0;
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5552_: u8 = 0;
    let mut v_fvarId_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5558_: u8 = 0;
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: u8 = 0;
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5568_: u8 = 0;
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v_fvarId_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5588_: u8 = 0;
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: u8 = 0;
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5607_: u8 = 0;
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5612_: u8 = 0;
    let mut v_fvarId_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: u8 = 0;
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5631_: u8 = 0;
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5634_: u8 = 0;
    let mut v_fvarId_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_5637_: u8 = 0;
    let mut v_persistent_5638_: u8 = 0;
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5641_: u8 = 0;
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: u8 = 0;
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5648_: u8 = 0;
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5655_: u8 = 0;
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5658_: u8 = 0;
    let mut v_fvarId_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_5661_: u8 = 0;
    let mut v_persistent_5662_: u8 = 0;
    let mut v_objs_x3f_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5666_: u8 = 0;
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5673_: u8 = 0;
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5680_: u8 = 0;
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5683_: u8 = 0;
    let mut v_fvarId_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: u8 = 0;
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5694_: u8 = 0;
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5701_: u8 = 0;
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_decl_5445_) {
                0 => {
                    v_decl_5453_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_isSharedCheck_5477_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5477_ == 0 {
                        v___x_5455_ = v_decl_5445_;
                        v_isShared_5456_ = v_isSharedCheck_5477_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_decl_5453_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5455_ = crate::leanh::lean_box(0);
                        v_isShared_5456_ = v_isSharedCheck_5477_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_decl_5478_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_isSharedCheck_5502_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5502_ == 0 {
                        v___x_5480_ = v_decl_5445_;
                        v_isShared_5481_ = v_isSharedCheck_5502_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_decl_5478_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5480_ = crate::leanh::lean_box(0);
                        v_isShared_5481_ = v_isSharedCheck_5502_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_decl_5503_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_isSharedCheck_5527_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5527_ == 0 {
                        v___x_5505_ = v_decl_5445_;
                        v_isShared_5506_ = v_isSharedCheck_5527_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_decl_5503_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5505_ = crate::leanh::lean_box(0);
                        v_isShared_5506_ = v_isSharedCheck_5527_;
                        state = 13;
                        continue;
                    }
                }
                3 => {
                    v_fvarId_5528_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_i_5529_ = crate::leanh::lean_ctor_get(v_decl_5445_, 1);
                    v_y_5530_ = crate::leanh::lean_ctor_get(v_decl_5445_, 2);
                    v_isSharedCheck_5552_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5552_ == 0 {
                        v___x_5532_ = v_decl_5445_;
                        v_isShared_5533_ = v_isSharedCheck_5552_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_y_5530_);
                        crate::leanh::lean_inc(v_i_5529_);
                        crate::leanh::lean_inc(v_fvarId_5528_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5532_ = crate::leanh::lean_box(0);
                        v_isShared_5533_ = v_isSharedCheck_5552_;
                        state = 19;
                        continue;
                    }
                }
                4 => {
                    v_fvarId_5553_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_i_5554_ = crate::leanh::lean_ctor_get(v_decl_5445_, 1);
                    v_y_5555_ = crate::leanh::lean_ctor_get(v_decl_5445_, 2);
                    v_isSharedCheck_5580_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5580_ == 0 {
                        v___x_5557_ = v_decl_5445_;
                        v_isShared_5558_ = v_isSharedCheck_5580_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_y_5555_);
                        crate::leanh::lean_inc(v_i_5554_);
                        crate::leanh::lean_inc(v_fvarId_5553_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5557_ = crate::leanh::lean_box(0);
                        v_isShared_5558_ = v_isSharedCheck_5580_;
                        state = 23;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_5581_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_i_5582_ = crate::leanh::lean_ctor_get(v_decl_5445_, 1);
                    v_offset_5583_ = crate::leanh::lean_ctor_get(v_decl_5445_, 2);
                    v_y_5584_ = crate::leanh::lean_ctor_get(v_decl_5445_, 3);
                    v_ty_5585_ = crate::leanh::lean_ctor_get(v_decl_5445_, 4);
                    v_isSharedCheck_5612_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5612_ == 0 {
                        v___x_5587_ = v_decl_5445_;
                        v_isShared_5588_ = v_isSharedCheck_5612_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_ty_5585_);
                        crate::leanh::lean_inc(v_y_5584_);
                        crate::leanh::lean_inc(v_offset_5583_);
                        crate::leanh::lean_inc(v_i_5582_);
                        crate::leanh::lean_inc(v_fvarId_5581_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5587_ = crate::leanh::lean_box(0);
                        v_isShared_5588_ = v_isSharedCheck_5612_;
                        state = 27;
                        continue;
                    }
                }
                6 => {
                    v_fvarId_5613_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_cidx_5614_ = crate::leanh::lean_ctor_get(v_decl_5445_, 1);
                    v_isSharedCheck_5634_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5634_ == 0 {
                        v___x_5616_ = v_decl_5445_;
                        v_isShared_5617_ = v_isSharedCheck_5634_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cidx_5614_);
                        crate::leanh::lean_inc(v_fvarId_5613_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5616_ = crate::leanh::lean_box(0);
                        v_isShared_5617_ = v_isSharedCheck_5634_;
                        state = 31;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_5635_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_n_5636_ = crate::leanh::lean_ctor_get(v_decl_5445_, 1);
                    v_check_5637_ = crate::leanh::lean_ctor_get_uint8(
                        v_decl_5445_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_persistent_5638_ = crate::leanh::lean_ctor_get_uint8(
                        v_decl_5445_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_5658_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5658_ == 0 {
                        v___x_5640_ = v_decl_5445_;
                        v_isShared_5641_ = v_isSharedCheck_5658_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_5636_);
                        crate::leanh::lean_inc(v_fvarId_5635_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5640_ = crate::leanh::lean_box(0);
                        v_isShared_5641_ = v_isSharedCheck_5658_;
                        state = 35;
                        continue;
                    }
                }
                8 => {
                    v_fvarId_5659_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_n_5660_ = crate::leanh::lean_ctor_get(v_decl_5445_, 1);
                    v_check_5661_ = crate::leanh::lean_ctor_get_uint8(
                        v_decl_5445_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_5662_ = crate::leanh::lean_ctor_get_uint8(
                        v_decl_5445_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_objs_x3f_5663_ = crate::leanh::lean_ctor_get(v_decl_5445_, 2);
                    v_isSharedCheck_5683_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5683_ == 0 {
                        v___x_5665_ = v_decl_5445_;
                        v_isShared_5666_ = v_isSharedCheck_5683_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_objs_x3f_5663_);
                        crate::leanh::lean_inc(v_n_5660_);
                        crate::leanh::lean_inc(v_fvarId_5659_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5665_ = crate::leanh::lean_box(0);
                        v_isShared_5666_ = v_isSharedCheck_5683_;
                        state = 39;
                        continue;
                    }
                }
                _ => {
                    v_fvarId_5684_ = crate::leanh::lean_ctor_get(v_decl_5445_, 0);
                    v_isSharedCheck_5704_ = (!crate::leanh::lean_is_exclusive(v_decl_5445_)) as u8;
                    if v_isSharedCheck_5704_ == 0 {
                        v___x_5686_ = v_decl_5445_;
                        v_isShared_5687_ = v_isSharedCheck_5704_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_5684_);
                        crate::leanh::lean_dec(v_decl_5445_);
                        v___x_5686_ = crate::leanh::lean_box(0);
                        v_isShared_5687_ = v_isSharedCheck_5704_;
                        state = 43;
                        continue;
                    }
                }
            },
            1 => {
                v___x_5457_ = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(
                    v_pu_5444_,
                    v_decl_5453_,
                    v_a_5446_,
                    v_a_5447_,
                    v_a_5448_,
                    v_a_5449_,
                    v_a_5450_,
                    v_a_5451_,
                );
                if crate::leanh::lean_obj_tag(v___x_5457_) == 0 {
                    v_a_5458_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                    v_isSharedCheck_5468_ = (!crate::leanh::lean_is_exclusive(v___x_5457_)) as u8;
                    if v_isSharedCheck_5468_ == 0 {
                        v___x_5460_ = v___x_5457_;
                        v_isShared_5461_ = v_isSharedCheck_5468_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5458_);
                        crate::leanh::lean_dec(v___x_5457_);
                        v___x_5460_ = crate::leanh::lean_box(0);
                        v_isShared_5461_ = v_isSharedCheck_5468_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5455_);
                    v_a_5469_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                    v_isSharedCheck_5476_ = (!crate::leanh::lean_is_exclusive(v___x_5457_)) as u8;
                    if v_isSharedCheck_5476_ == 0 {
                        v___x_5471_ = v___x_5457_;
                        v_isShared_5472_ = v_isSharedCheck_5476_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5469_);
                        crate::leanh::lean_dec(v___x_5457_);
                        v___x_5471_ = crate::leanh::lean_box(0);
                        v_isShared_5472_ = v_isSharedCheck_5476_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5456_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5455_, 0, v_a_5458_);
                    v___x_5463_ = v___x_5455_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_a_5458_);
                    v___x_5463_ = v_reuseFailAlloc_5467_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5460_, 0, v___x_5463_);
                    v___x_5465_ = v___x_5460_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5463_);
                    v___x_5465_ = v_reuseFailAlloc_5466_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5465_;
            }
            5 => {
                if v_isShared_5472_ == 0 {
                    v___x_5474_ = v___x_5471_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5469_);
                    v___x_5474_ = v_reuseFailAlloc_5475_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5474_;
            }
            7 => {
                v___x_5482_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(
                    v_pu_5444_,
                    v_decl_5478_,
                    v_a_5446_,
                    v_a_5447_,
                    v_a_5448_,
                    v_a_5449_,
                    v_a_5450_,
                    v_a_5451_,
                );
                if crate::leanh::lean_obj_tag(v___x_5482_) == 0 {
                    v_a_5483_ = crate::leanh::lean_ctor_get(v___x_5482_, 0);
                    v_isSharedCheck_5493_ = (!crate::leanh::lean_is_exclusive(v___x_5482_)) as u8;
                    if v_isSharedCheck_5493_ == 0 {
                        v___x_5485_ = v___x_5482_;
                        v_isShared_5486_ = v_isSharedCheck_5493_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5483_);
                        crate::leanh::lean_dec(v___x_5482_);
                        v___x_5485_ = crate::leanh::lean_box(0);
                        v_isShared_5486_ = v_isSharedCheck_5493_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5480_);
                    v_a_5494_ = crate::leanh::lean_ctor_get(v___x_5482_, 0);
                    v_isSharedCheck_5501_ = (!crate::leanh::lean_is_exclusive(v___x_5482_)) as u8;
                    if v_isSharedCheck_5501_ == 0 {
                        v___x_5496_ = v___x_5482_;
                        v_isShared_5497_ = v_isSharedCheck_5501_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5494_);
                        crate::leanh::lean_dec(v___x_5482_);
                        v___x_5496_ = crate::leanh::lean_box(0);
                        v_isShared_5497_ = v_isSharedCheck_5501_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5480_, 0, v_a_5483_);
                    v___x_5488_ = v___x_5480_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5483_);
                    v___x_5488_ = v_reuseFailAlloc_5492_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5486_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5485_, 0, v___x_5488_);
                    v___x_5490_ = v___x_5485_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5488_);
                    v___x_5490_ = v_reuseFailAlloc_5491_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5490_;
            }
            11 => {
                if v_isShared_5497_ == 0 {
                    v___x_5499_ = v___x_5496_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5494_);
                    v___x_5499_ = v_reuseFailAlloc_5500_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5499_;
            }
            13 => {
                v___x_5507_ = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(
                    v_pu_5444_,
                    v_decl_5503_,
                    v_a_5446_,
                    v_a_5447_,
                    v_a_5448_,
                    v_a_5449_,
                    v_a_5450_,
                    v_a_5451_,
                );
                if crate::leanh::lean_obj_tag(v___x_5507_) == 0 {
                    v_a_5508_ = crate::leanh::lean_ctor_get(v___x_5507_, 0);
                    v_isSharedCheck_5518_ = (!crate::leanh::lean_is_exclusive(v___x_5507_)) as u8;
                    if v_isSharedCheck_5518_ == 0 {
                        v___x_5510_ = v___x_5507_;
                        v_isShared_5511_ = v_isSharedCheck_5518_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5508_);
                        crate::leanh::lean_dec(v___x_5507_);
                        v___x_5510_ = crate::leanh::lean_box(0);
                        v_isShared_5511_ = v_isSharedCheck_5518_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5505_);
                    v_a_5519_ = crate::leanh::lean_ctor_get(v___x_5507_, 0);
                    v_isSharedCheck_5526_ = (!crate::leanh::lean_is_exclusive(v___x_5507_)) as u8;
                    if v_isSharedCheck_5526_ == 0 {
                        v___x_5521_ = v___x_5507_;
                        v_isShared_5522_ = v_isSharedCheck_5526_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5519_);
                        crate::leanh::lean_dec(v___x_5507_);
                        v___x_5521_ = crate::leanh::lean_box(0);
                        v_isShared_5522_ = v_isSharedCheck_5526_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_5506_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5505_, 0, v_a_5508_);
                    v___x_5513_ = v___x_5505_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5517_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5508_);
                    v___x_5513_ = v_reuseFailAlloc_5517_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_5511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5510_, 0, v___x_5513_);
                    v___x_5515_ = v___x_5510_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5513_);
                    v___x_5515_ = v_reuseFailAlloc_5516_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5515_;
            }
            17 => {
                if v_isShared_5522_ == 0 {
                    v___x_5524_ = v___x_5521_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
                    v___x_5524_ = v_reuseFailAlloc_5525_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5524_;
            }
            19 => {
                v___x_5534_ = lean_st_ref_get(v_a_5447_);
                v___x_5535_ = 1;
                v___x_5536_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5534_,
                    v_fvarId_5528_,
                    v___x_5535_,
                );
                crate::leanh::lean_dec(v___x_5534_);
                if crate::leanh::lean_obj_tag(v___x_5536_) == 0 {
                    v_fvarId_5537_ = crate::leanh::lean_ctor_get(v___x_5536_, 0);
                    v_isSharedCheck_5549_ = (!crate::leanh::lean_is_exclusive(v___x_5536_)) as u8;
                    if v_isSharedCheck_5549_ == 0 {
                        v___x_5539_ = v___x_5536_;
                        v_isShared_5540_ = v_isSharedCheck_5549_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_5537_);
                        crate::leanh::lean_dec(v___x_5536_);
                        v___x_5539_ = crate::leanh::lean_box(0);
                        v_isShared_5540_ = v_isSharedCheck_5549_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5536_);
                    crate::leanh::lean_del_object(v___x_5532_);
                    crate::leanh::lean_dec(v_y_5530_);
                    crate::leanh::lean_dec(v_i_5529_);
                    v___x_5550_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1,
                    );
                    v___x_5551_ =
                        l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(
                            v_pu_5444_,
                            v___x_5550_,
                            v_a_5446_,
                            v_a_5447_,
                            v_a_5448_,
                            v_a_5449_,
                            v_a_5450_,
                            v_a_5451_,
                        );
                    return v___x_5551_;
                }
            }
            20 => {
                v___x_5541_ = lean_st_ref_get(v_a_5447_);
                v___x_5542_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
                        v_pu_5444_,
                        v___x_5541_,
                        v_y_5530_,
                        v___x_5535_,
                    );
                crate::leanh::lean_dec(v___x_5541_);
                if v_isShared_5533_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5532_, 2, v___x_5542_);
                    crate::leanh::lean_ctor_set(v___x_5532_, 0, v_fvarId_5537_);
                    v___x_5544_ = v___x_5532_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5548_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_fvarId_5537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_i_5529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5548_, 2, v___x_5542_);
                    v___x_5544_ = v_reuseFailAlloc_5548_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_5540_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5539_, 0, v___x_5544_);
                    v___x_5546_ = v___x_5539_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5544_);
                    v___x_5546_ = v_reuseFailAlloc_5547_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5546_;
            }
            23 => {
                v___x_5559_ = lean_st_ref_get(v_a_5447_);
                v___x_5560_ = 1;
                v___x_5561_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5559_,
                    v_fvarId_5553_,
                    v___x_5560_,
                );
                crate::leanh::lean_dec(v___x_5559_);
                if crate::leanh::lean_obj_tag(v___x_5561_) == 0 {
                    v_fvarId_5562_ = crate::leanh::lean_ctor_get(v___x_5561_, 0);
                    crate::leanh::lean_inc(v_fvarId_5562_);
                    crate::leanh::lean_dec_ref_known(v___x_5561_, 1);
                    v___x_5563_ = lean_st_ref_get(v_a_5447_);
                    v___x_5564_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_5563_,
                        v_y_5555_,
                        v___x_5560_,
                    );
                    crate::leanh::lean_dec(v___x_5563_);
                    if crate::leanh::lean_obj_tag(v___x_5564_) == 0 {
                        v_fvarId_5565_ = crate::leanh::lean_ctor_get(v___x_5564_, 0);
                        v_isSharedCheck_5575_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5564_)) as u8;
                        if v_isSharedCheck_5575_ == 0 {
                            v___x_5567_ = v___x_5564_;
                            v_isShared_5568_ = v_isSharedCheck_5575_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_5565_);
                            crate::leanh::lean_dec(v___x_5564_);
                            v___x_5567_ = crate::leanh::lean_box(0);
                            v_isShared_5568_ = v_isSharedCheck_5575_;
                            state = 24;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5564_);
                        crate::leanh::lean_dec(v_fvarId_5562_);
                        crate::leanh::lean_del_object(v___x_5557_);
                        crate::leanh::lean_dec(v_i_5554_);
                        v___x_5576_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once), _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
                        v___x_5577_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_5444_, v___x_5576_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_);
                        return v___x_5577_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5561_);
                    crate::leanh::lean_del_object(v___x_5557_);
                    crate::leanh::lean_dec(v_y_5555_);
                    crate::leanh::lean_dec(v_i_5554_);
                    v___x_5578_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3,
                    );
                    v___x_5579_ =
                        l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(
                            v_pu_5444_,
                            v___x_5578_,
                            v_a_5446_,
                            v_a_5447_,
                            v_a_5448_,
                            v_a_5449_,
                            v_a_5450_,
                            v_a_5451_,
                        );
                    return v___x_5579_;
                }
            }
            24 => {
                if v_isShared_5558_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5557_, 2, v_fvarId_5565_);
                    crate::leanh::lean_ctor_set(v___x_5557_, 0, v_fvarId_5562_);
                    v___x_5570_ = v___x_5557_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5574_ = crate::leanh::lean_alloc_ctor(4, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_fvarId_5562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 1, v_i_5554_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 2, v_fvarId_5565_);
                    v___x_5570_ = v_reuseFailAlloc_5574_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_5568_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5567_, 0, v___x_5570_);
                    v___x_5572_ = v___x_5567_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5570_);
                    v___x_5572_ = v_reuseFailAlloc_5573_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5572_;
            }
            27 => {
                v___x_5589_ = lean_st_ref_get(v_a_5447_);
                v___x_5590_ = 1;
                v___x_5591_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5589_,
                    v_fvarId_5581_,
                    v___x_5590_,
                );
                crate::leanh::lean_dec(v___x_5589_);
                if crate::leanh::lean_obj_tag(v___x_5591_) == 0 {
                    v_fvarId_5592_ = crate::leanh::lean_ctor_get(v___x_5591_, 0);
                    crate::leanh::lean_inc(v_fvarId_5592_);
                    crate::leanh::lean_dec_ref_known(v___x_5591_, 1);
                    v___x_5593_ = lean_st_ref_get(v_a_5447_);
                    v___x_5594_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v___x_5593_,
                        v_y_5584_,
                        v___x_5590_,
                    );
                    crate::leanh::lean_dec(v___x_5593_);
                    if crate::leanh::lean_obj_tag(v___x_5594_) == 0 {
                        v_fvarId_5595_ = crate::leanh::lean_ctor_get(v___x_5594_, 0);
                        v_isSharedCheck_5607_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5594_)) as u8;
                        if v_isSharedCheck_5607_ == 0 {
                            v___x_5597_ = v___x_5594_;
                            v_isShared_5598_ = v_isSharedCheck_5607_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_5595_);
                            crate::leanh::lean_dec(v___x_5594_);
                            v___x_5597_ = crate::leanh::lean_box(0);
                            v_isShared_5598_ = v_isSharedCheck_5607_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5594_);
                        crate::leanh::lean_dec(v_fvarId_5592_);
                        crate::leanh::lean_del_object(v___x_5587_);
                        crate::leanh::lean_dec_ref(v_ty_5585_);
                        crate::leanh::lean_dec(v_offset_5583_);
                        crate::leanh::lean_dec(v_i_5582_);
                        v___x_5608_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once), _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
                        v___x_5609_ = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(v_pu_5444_, v___x_5608_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_);
                        return v___x_5609_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5591_);
                    crate::leanh::lean_del_object(v___x_5587_);
                    crate::leanh::lean_dec_ref(v_ty_5585_);
                    crate::leanh::lean_dec(v_y_5584_);
                    crate::leanh::lean_dec(v_offset_5583_);
                    crate::leanh::lean_dec(v_i_5582_);
                    v___x_5610_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5,
                    );
                    v___x_5611_ =
                        l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(
                            v_pu_5444_,
                            v___x_5610_,
                            v_a_5446_,
                            v_a_5447_,
                            v_a_5448_,
                            v_a_5449_,
                            v_a_5450_,
                            v_a_5451_,
                        );
                    return v___x_5611_;
                }
            }
            28 => {
                v___x_5599_ = lean_st_ref_get(v_a_5447_);
                v___x_5600_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v_pu_5444_,
                        v___x_5599_,
                        v___x_5590_,
                        v_ty_5585_,
                    );
                crate::leanh::lean_dec(v___x_5599_);
                if v_isShared_5588_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5587_, 4, v___x_5600_);
                    crate::leanh::lean_ctor_set(v___x_5587_, 3, v_fvarId_5595_);
                    crate::leanh::lean_ctor_set(v___x_5587_, 0, v_fvarId_5592_);
                    v___x_5602_ = v___x_5587_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5606_ = crate::leanh::lean_alloc_ctor(5, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_fvarId_5592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 1, v_i_5582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 2, v_offset_5583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 3, v_fvarId_5595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5606_, 4, v___x_5600_);
                    v___x_5602_ = v_reuseFailAlloc_5606_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_5598_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5597_, 0, v___x_5602_);
                    v___x_5604_ = v___x_5597_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
                    v___x_5604_ = v_reuseFailAlloc_5605_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5604_;
            }
            31 => {
                v___x_5618_ = lean_st_ref_get(v_a_5447_);
                v___x_5619_ = 1;
                v___x_5620_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5618_,
                    v_fvarId_5613_,
                    v___x_5619_,
                );
                crate::leanh::lean_dec(v___x_5618_);
                if crate::leanh::lean_obj_tag(v___x_5620_) == 0 {
                    v_fvarId_5621_ = crate::leanh::lean_ctor_get(v___x_5620_, 0);
                    v_isSharedCheck_5631_ = (!crate::leanh::lean_is_exclusive(v___x_5620_)) as u8;
                    if v_isSharedCheck_5631_ == 0 {
                        v___x_5623_ = v___x_5620_;
                        v_isShared_5624_ = v_isSharedCheck_5631_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_5621_);
                        crate::leanh::lean_dec(v___x_5620_);
                        v___x_5623_ = crate::leanh::lean_box(0);
                        v_isShared_5624_ = v_isSharedCheck_5631_;
                        state = 32;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5620_);
                    crate::leanh::lean_del_object(v___x_5616_);
                    crate::leanh::lean_dec(v_cidx_5614_);
                    v___x_5632_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6,
                    );
                    v___x_5633_ =
                        l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(
                            v_pu_5444_,
                            v___x_5632_,
                            v_a_5446_,
                            v_a_5447_,
                            v_a_5448_,
                            v_a_5449_,
                            v_a_5450_,
                            v_a_5451_,
                        );
                    return v___x_5633_;
                }
            }
            32 => {
                if v_isShared_5617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5616_, 0, v_fvarId_5621_);
                    v___x_5626_ = v___x_5616_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5630_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_fvarId_5621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5630_, 1, v_cidx_5614_);
                    v___x_5626_ = v_reuseFailAlloc_5630_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                if v_isShared_5624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5623_, 0, v___x_5626_);
                    v___x_5628_ = v___x_5623_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5629_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 0, v___x_5626_);
                    v___x_5628_ = v_reuseFailAlloc_5629_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5628_;
            }
            35 => {
                v___x_5642_ = lean_st_ref_get(v_a_5447_);
                v___x_5643_ = 1;
                v___x_5644_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5642_,
                    v_fvarId_5635_,
                    v___x_5643_,
                );
                crate::leanh::lean_dec(v___x_5642_);
                if crate::leanh::lean_obj_tag(v___x_5644_) == 0 {
                    v_fvarId_5645_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
                    v_isSharedCheck_5655_ = (!crate::leanh::lean_is_exclusive(v___x_5644_)) as u8;
                    if v_isSharedCheck_5655_ == 0 {
                        v___x_5647_ = v___x_5644_;
                        v_isShared_5648_ = v_isSharedCheck_5655_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_5645_);
                        crate::leanh::lean_dec(v___x_5644_);
                        v___x_5647_ = crate::leanh::lean_box(0);
                        v_isShared_5648_ = v_isSharedCheck_5655_;
                        state = 36;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5644_);
                    crate::leanh::lean_del_object(v___x_5640_);
                    crate::leanh::lean_dec(v_n_5636_);
                    v___x_5656_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7,
                    );
                    v___x_5657_ =
                        l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(
                            v_pu_5444_,
                            v___x_5656_,
                            v_a_5446_,
                            v_a_5447_,
                            v_a_5448_,
                            v_a_5449_,
                            v_a_5450_,
                            v_a_5451_,
                        );
                    return v___x_5657_;
                }
            }
            36 => {
                if v_isShared_5641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5640_, 0, v_fvarId_5645_);
                    v___x_5650_ = v___x_5640_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5654_ = crate::leanh::lean_alloc_ctor(7, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5654_, 0, v_fvarId_5645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5654_, 1, v_n_5636_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5654_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_check_5637_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5654_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_persistent_5638_,
                    );
                    v___x_5650_ = v_reuseFailAlloc_5654_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_5648_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5647_, 0, v___x_5650_);
                    v___x_5652_ = v___x_5647_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5653_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5653_, 0, v___x_5650_);
                    v___x_5652_ = v_reuseFailAlloc_5653_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5652_;
            }
            39 => {
                v___x_5667_ = lean_st_ref_get(v_a_5447_);
                v___x_5668_ = 1;
                v___x_5669_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5667_,
                    v_fvarId_5659_,
                    v___x_5668_,
                );
                crate::leanh::lean_dec(v___x_5667_);
                if crate::leanh::lean_obj_tag(v___x_5669_) == 0 {
                    v_fvarId_5670_ = crate::leanh::lean_ctor_get(v___x_5669_, 0);
                    v_isSharedCheck_5680_ = (!crate::leanh::lean_is_exclusive(v___x_5669_)) as u8;
                    if v_isSharedCheck_5680_ == 0 {
                        v___x_5672_ = v___x_5669_;
                        v_isShared_5673_ = v_isSharedCheck_5680_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_5670_);
                        crate::leanh::lean_dec(v___x_5669_);
                        v___x_5672_ = crate::leanh::lean_box(0);
                        v_isShared_5673_ = v_isSharedCheck_5680_;
                        state = 40;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5669_);
                    crate::leanh::lean_del_object(v___x_5665_);
                    crate::leanh::lean_dec(v_objs_x3f_5663_);
                    crate::leanh::lean_dec(v_n_5660_);
                    v___x_5681_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8,
                    );
                    v___x_5682_ =
                        l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(
                            v_pu_5444_,
                            v___x_5681_,
                            v_a_5446_,
                            v_a_5447_,
                            v_a_5448_,
                            v_a_5449_,
                            v_a_5450_,
                            v_a_5451_,
                        );
                    return v___x_5682_;
                }
            }
            40 => {
                if v_isShared_5666_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5665_, 0, v_fvarId_5670_);
                    v___x_5675_ = v___x_5665_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5679_ = crate::leanh::lean_alloc_ctor(8, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_fvarId_5670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5679_, 1, v_n_5660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5679_, 2, v_objs_x3f_5663_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5679_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_check_5661_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5679_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_5662_,
                    );
                    v___x_5675_ = v_reuseFailAlloc_5679_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_5673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5672_, 0, v___x_5675_);
                    v___x_5677_ = v___x_5672_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_5678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5678_, 0, v___x_5675_);
                    v___x_5677_ = v_reuseFailAlloc_5678_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_5677_;
            }
            43 => {
                v___x_5688_ = lean_st_ref_get(v_a_5447_);
                v___x_5689_ = 1;
                v___x_5690_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v___x_5688_,
                    v_fvarId_5684_,
                    v___x_5689_,
                );
                crate::leanh::lean_dec(v___x_5688_);
                if crate::leanh::lean_obj_tag(v___x_5690_) == 0 {
                    v_fvarId_5691_ = crate::leanh::lean_ctor_get(v___x_5690_, 0);
                    v_isSharedCheck_5701_ = (!crate::leanh::lean_is_exclusive(v___x_5690_)) as u8;
                    if v_isSharedCheck_5701_ == 0 {
                        v___x_5693_ = v___x_5690_;
                        v_isShared_5694_ = v_isSharedCheck_5701_;
                        state = 44;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_5691_);
                        crate::leanh::lean_dec(v___x_5690_);
                        v___x_5693_ = crate::leanh::lean_box(0);
                        v_isShared_5694_ = v_isSharedCheck_5701_;
                        state = 44;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5690_);
                    crate::leanh::lean_del_object(v___x_5686_);
                    v___x_5702_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9,
                    );
                    v___x_5703_ =
                        l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(
                            v_pu_5444_,
                            v___x_5702_,
                            v_a_5446_,
                            v_a_5447_,
                            v_a_5448_,
                            v_a_5449_,
                            v_a_5450_,
                            v_a_5451_,
                        );
                    return v___x_5703_;
                }
            }
            44 => {
                if v_isShared_5687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5686_, 0, v_fvarId_5691_);
                    v___x_5696_ = v___x_5686_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_5700_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_fvarId_5691_);
                    v___x_5696_ = v_reuseFailAlloc_5700_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_5694_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5693_, 0, v___x_5696_);
                    v___x_5698_ = v___x_5693_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_5699_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5699_, 0, v___x_5696_);
                    v___x_5698_ = v_reuseFailAlloc_5699_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_5698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(
    mut v_pu_5705_: *mut crate::leanh::LeanObject,
    mut v_decl_5706_: *mut crate::leanh::LeanObject,
    mut v_a_5707_: *mut crate::leanh::LeanObject,
    mut v_a_5708_: *mut crate::leanh::LeanObject,
    mut v_a_5709_: *mut crate::leanh::LeanObject,
    mut v_a_5710_: *mut crate::leanh::LeanObject,
    mut v_a_5711_: *mut crate::leanh::LeanObject,
    mut v_a_5712_: *mut crate::leanh::LeanObject,
    mut v_a_5713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5714_: u8 = 0;
    let mut v_a_boxed_5715_: u8 = 0;
    let mut v_res_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5714_ = (crate::leanh::lean_unbox(v_pu_5705_) as u8);
    v_a_boxed_5715_ = (crate::leanh::lean_unbox(v_a_5707_) as u8);
    v_res_5716_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(
        v_pu_boxed_5714_,
        v_decl_5706_,
        v_a_boxed_5715_,
        v_a_5708_,
        v_a_5709_,
        v_a_5710_,
        v_a_5711_,
        v_a_5712_,
    );
    crate::leanh::lean_dec(v_a_5712_);
    crate::leanh::lean_dec_ref(v_a_5711_);
    crate::leanh::lean_dec(v_a_5710_);
    crate::leanh::lean_dec_ref(v_a_5709_);
    crate::leanh::lean_dec(v_a_5708_);
    return v_res_5716_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_internalize(
    mut v_pu_5717_: u8,
    mut v_code_5718_: *mut crate::leanh::LeanObject,
    mut v_s_5719_: *mut crate::leanh::LeanObject,
    mut v_uniqueIdents_5720_: u8,
    mut v_a_5721_: *mut crate::leanh::LeanObject,
    mut v_a_5722_: *mut crate::leanh::LeanObject,
    mut v_a_5723_: *mut crate::leanh::LeanObject,
    mut v_a_5724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5731_: u8 = 0;
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5726_ = lean_st_mk_ref(v_s_5719_);
                v___x_5727_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                    v_pu_5717_,
                    v_code_5718_,
                    v_uniqueIdents_5720_,
                    v___x_5726_,
                    v_a_5721_,
                    v_a_5722_,
                    v_a_5723_,
                    v_a_5724_,
                );
                if crate::leanh::lean_obj_tag(v___x_5727_) == 0 {
                    v_a_5728_ = crate::leanh::lean_ctor_get(v___x_5727_, 0);
                    v_isSharedCheck_5736_ = (!crate::leanh::lean_is_exclusive(v___x_5727_)) as u8;
                    if v_isSharedCheck_5736_ == 0 {
                        v___x_5730_ = v___x_5727_;
                        v_isShared_5731_ = v_isSharedCheck_5736_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5728_);
                        crate::leanh::lean_dec(v___x_5727_);
                        v___x_5730_ = crate::leanh::lean_box(0);
                        v_isShared_5731_ = v_isSharedCheck_5736_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5726_);
                    return v___x_5727_;
                }
            }
            1 => {
                v___x_5732_ = lean_st_ref_get(v___x_5726_);
                crate::leanh::lean_dec(v___x_5726_);
                crate::leanh::lean_dec(v___x_5732_);
                if v_isShared_5731_ == 0 {
                    v___x_5734_ = v___x_5730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5728_);
                    v___x_5734_ = v_reuseFailAlloc_5735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_internalize___boxed(
    mut v_pu_5737_: *mut crate::leanh::LeanObject,
    mut v_code_5738_: *mut crate::leanh::LeanObject,
    mut v_s_5739_: *mut crate::leanh::LeanObject,
    mut v_uniqueIdents_5740_: *mut crate::leanh::LeanObject,
    mut v_a_5741_: *mut crate::leanh::LeanObject,
    mut v_a_5742_: *mut crate::leanh::LeanObject,
    mut v_a_5743_: *mut crate::leanh::LeanObject,
    mut v_a_5744_: *mut crate::leanh::LeanObject,
    mut v_a_5745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5746_: u8 = 0;
    let mut v_uniqueIdents_boxed_5747_: u8 = 0;
    let mut v_res_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5746_ = (crate::leanh::lean_unbox(v_pu_5737_) as u8);
    v_uniqueIdents_boxed_5747_ = (crate::leanh::lean_unbox(v_uniqueIdents_5740_) as u8);
    v_res_5748_ = l_Lean_Compiler_LCNF_Code_internalize(
        v_pu_boxed_5746_,
        v_code_5738_,
        v_s_5739_,
        v_uniqueIdents_boxed_5747_,
        v_a_5741_,
        v_a_5742_,
        v_a_5743_,
        v_a_5744_,
    );
    crate::leanh::lean_dec(v_a_5744_);
    crate::leanh::lean_dec_ref(v_a_5743_);
    crate::leanh::lean_dec(v_a_5742_);
    crate::leanh::lean_dec_ref(v_a_5741_);
    return v_res_5748_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(
    mut v_f_5749_: *mut crate::leanh::LeanObject,
    mut v_v_5750_: *mut crate::leanh::LeanObject,
    mut v___y_5751_: u8,
    mut v___y_5752_: *mut crate::leanh::LeanObject,
    mut v___y_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
    mut v___y_5755_: *mut crate::leanh::LeanObject,
    mut v___y_5756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5761_: u8 = 0;
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5767_: u8 = 0;
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5774_: u8 = 0;
    let mut v_a_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5778_: u8 = 0;
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5782_: u8 = 0;
    let mut v_isSharedCheck_5783_: u8 = 0;
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_5750_) == 0 {
                    v_code_5758_ = crate::leanh::lean_ctor_get(v_v_5750_, 0);
                    v_isSharedCheck_5783_ = (!crate::leanh::lean_is_exclusive(v_v_5750_)) as u8;
                    if v_isSharedCheck_5783_ == 0 {
                        v___x_5760_ = v_v_5750_;
                        v_isShared_5761_ = v_isSharedCheck_5783_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_5758_);
                        crate::leanh::lean_dec(v_v_5750_);
                        v___x_5760_ = crate::leanh::lean_box(0);
                        v_isShared_5761_ = v_isSharedCheck_5783_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5749_);
                    v___x_5784_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5784_, 0, v_v_5750_);
                    return v___x_5784_;
                }
            }
            1 => {
                v___x_5762_ = crate::leanh::lean_box((v___y_5751_) as usize);
                crate::leanh::lean_inc(v___y_5756_);
                crate::leanh::lean_inc_ref(v___y_5755_);
                crate::leanh::lean_inc(v___y_5754_);
                crate::leanh::lean_inc_ref(v___y_5753_);
                crate::leanh::lean_inc(v___y_5752_);
                v___x_5763_ = crate::leanh::lean_apply_8(
                    v_f_5749_,
                    v_code_5758_,
                    v___x_5762_,
                    v___y_5752_,
                    v___y_5753_,
                    v___y_5754_,
                    v___y_5755_,
                    v___y_5756_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5763_) == 0 {
                    v_a_5764_ = crate::leanh::lean_ctor_get(v___x_5763_, 0);
                    v_isSharedCheck_5774_ = (!crate::leanh::lean_is_exclusive(v___x_5763_)) as u8;
                    if v_isSharedCheck_5774_ == 0 {
                        v___x_5766_ = v___x_5763_;
                        v_isShared_5767_ = v_isSharedCheck_5774_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5764_);
                        crate::leanh::lean_dec(v___x_5763_);
                        v___x_5766_ = crate::leanh::lean_box(0);
                        v_isShared_5767_ = v_isSharedCheck_5774_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5760_);
                    v_a_5775_ = crate::leanh::lean_ctor_get(v___x_5763_, 0);
                    v_isSharedCheck_5782_ = (!crate::leanh::lean_is_exclusive(v___x_5763_)) as u8;
                    if v_isSharedCheck_5782_ == 0 {
                        v___x_5777_ = v___x_5763_;
                        v_isShared_5778_ = v_isSharedCheck_5782_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5775_);
                        crate::leanh::lean_dec(v___x_5763_);
                        v___x_5777_ = crate::leanh::lean_box(0);
                        v_isShared_5778_ = v_isSharedCheck_5782_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5761_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5760_, 0, v_a_5764_);
                    v___x_5769_ = v___x_5760_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5773_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_a_5764_);
                    v___x_5769_ = v_reuseFailAlloc_5773_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5767_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5766_, 0, v___x_5769_);
                    v___x_5771_ = v___x_5766_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5772_, 0, v___x_5769_);
                    v___x_5771_ = v_reuseFailAlloc_5772_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5771_;
            }
            5 => {
                if v_isShared_5778_ == 0 {
                    v___x_5780_ = v___x_5777_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_a_5775_);
                    v___x_5780_ = v_reuseFailAlloc_5781_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(
    mut v_f_5785_: *mut crate::leanh::LeanObject,
    mut v_v_5786_: *mut crate::leanh::LeanObject,
    mut v___y_5787_: *mut crate::leanh::LeanObject,
    mut v___y_5788_: *mut crate::leanh::LeanObject,
    mut v___y_5789_: *mut crate::leanh::LeanObject,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1412__boxed_5794_: u8 = 0;
    let mut v_res_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_1412__boxed_5794_ = (crate::leanh::lean_unbox(v___y_5787_) as u8);
    v_res_5795_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_5785_, v_v_5786_, v___y_1412__boxed_5794_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_);
    crate::leanh::lean_dec(v___y_5792_);
    crate::leanh::lean_dec_ref(v___y_5791_);
    crate::leanh::lean_dec(v___y_5790_);
    crate::leanh::lean_dec_ref(v___y_5789_);
    crate::leanh::lean_dec(v___y_5788_);
    return v_res_5795_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(
    mut v_pu_5796_: u8,
    mut v_f_5797_: *mut crate::leanh::LeanObject,
    mut v_v_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: u8,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
    mut v___y_5801_: *mut crate::leanh::LeanObject,
    mut v___y_5802_: *mut crate::leanh::LeanObject,
    mut v___y_5803_: *mut crate::leanh::LeanObject,
    mut v___y_5804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5806_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v_f_5797_, v_v_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_);
    return v___x_5806_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(
    mut v_pu_5807_: *mut crate::leanh::LeanObject,
    mut v_f_5808_: *mut crate::leanh::LeanObject,
    mut v_v_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
    mut v___y_5812_: *mut crate::leanh::LeanObject,
    mut v___y_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
    mut v___y_5815_: *mut crate::leanh::LeanObject,
    mut v___y_5816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5817_: u8 = 0;
    let mut v___y_1488__boxed_5818_: u8 = 0;
    let mut v_res_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5817_ = (crate::leanh::lean_unbox(v_pu_5807_) as u8);
    v___y_1488__boxed_5818_ = (crate::leanh::lean_unbox(v___y_5810_) as u8);
    v_res_5819_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(v_pu_boxed_5817_, v_f_5808_, v_v_5809_, v___y_1488__boxed_5818_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
    crate::leanh::lean_dec(v___y_5815_);
    crate::leanh::lean_dec_ref(v___y_5814_);
    crate::leanh::lean_dec(v___y_5813_);
    crate::leanh::lean_dec_ref(v___y_5812_);
    crate::leanh::lean_dec(v___y_5811_);
    return v_res_5819_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(
    mut v_pu_5820_: u8,
    mut v_decl_5821_: *mut crate::leanh::LeanObject,
    mut v_a_5822_: u8,
    mut v_a_5823_: *mut crate::leanh::LeanObject,
    mut v_a_5824_: *mut crate::leanh::LeanObject,
    mut v_a_5825_: *mut crate::leanh::LeanObject,
    mut v_a_5826_: *mut crate::leanh::LeanObject,
    mut v_a_5827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_5831_: u8 = 0;
    let mut v_inlineAttr_x3f_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5835_: u8 = 0;
    let mut v_name_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_5840_: u8 = 0;
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5843_: u8 = 0;
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5846_: usize = 0;
    let mut v___x_5847_: usize = 0;
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5866_: u8 = 0;
    let mut v_a_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5870_: u8 = 0;
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5874_: u8 = 0;
    let mut v_a_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5878_: u8 = 0;
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5882_: u8 = 0;
    let mut v_a_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5886_: u8 = 0;
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5890_: u8 = 0;
    let mut v_isSharedCheck_5891_: u8 = 0;
    let mut v_isSharedCheck_5892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_5829_ = crate::leanh::lean_ctor_get(v_decl_5821_, 0);
                v_value_5830_ = crate::leanh::lean_ctor_get(v_decl_5821_, 1);
                v_recursive_5831_ = crate::leanh::lean_ctor_get_uint8(
                    v_decl_5821_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_5832_ = crate::leanh::lean_ctor_get(v_decl_5821_, 2);
                v_isSharedCheck_5892_ = (!crate::leanh::lean_is_exclusive(v_decl_5821_)) as u8;
                if v_isSharedCheck_5892_ == 0 {
                    v___x_5834_ = v_decl_5821_;
                    v_isShared_5835_ = v_isSharedCheck_5892_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_5832_);
                    crate::leanh::lean_inc(v_value_5830_);
                    crate::leanh::lean_inc(v_toSignature_5829_);
                    crate::leanh::lean_dec(v_decl_5821_);
                    v___x_5834_ = crate::leanh::lean_box(0);
                    v_isShared_5835_ = v_isSharedCheck_5892_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_5836_ = crate::leanh::lean_ctor_get(v_toSignature_5829_, 0);
                v_levelParams_5837_ = crate::leanh::lean_ctor_get(v_toSignature_5829_, 1);
                v_type_5838_ = crate::leanh::lean_ctor_get(v_toSignature_5829_, 2);
                v_params_5839_ = crate::leanh::lean_ctor_get(v_toSignature_5829_, 3);
                v_safe_5840_ = crate::leanh::lean_ctor_get_uint8(
                    v_toSignature_5829_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_5891_ =
                    (!crate::leanh::lean_is_exclusive(v_toSignature_5829_)) as u8;
                if v_isSharedCheck_5891_ == 0 {
                    v___x_5842_ = v_toSignature_5829_;
                    v_isShared_5843_ = v_isSharedCheck_5891_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_params_5839_);
                    crate::leanh::lean_inc(v_type_5838_);
                    crate::leanh::lean_inc(v_levelParams_5837_);
                    crate::leanh::lean_inc(v_name_5836_);
                    crate::leanh::lean_dec(v_toSignature_5829_);
                    v___x_5842_ = crate::leanh::lean_box(0);
                    v_isShared_5843_ = v_isSharedCheck_5891_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5844_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(v_pu_5820_, v_type_5838_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_);
                if crate::leanh::lean_obj_tag(v___x_5844_) == 0 {
                    v_a_5845_ = crate::leanh::lean_ctor_get(v___x_5844_, 0);
                    crate::leanh::lean_inc(v_a_5845_);
                    crate::leanh::lean_dec_ref_known(v___x_5844_, 1);
                    v_sz_5846_ = lean_array_size(v_params_5839_);
                    v___x_5847_ = 0usize;
                    v___x_5848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(v_pu_5820_, v_sz_5846_, v___x_5847_, v_params_5839_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_);
                    if crate::leanh::lean_obj_tag(v___x_5848_) == 0 {
                        v_a_5849_ = crate::leanh::lean_ctor_get(v___x_5848_, 0);
                        crate::leanh::lean_inc(v_a_5849_);
                        crate::leanh::lean_dec_ref_known(v___x_5848_, 1);
                        v___x_5850_ = crate::leanh::lean_box((v_pu_5820_) as usize);
                        v___x_5851_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed
                                as *mut core::ffi::c_void,
                            9,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_5851_, 0, v___x_5850_);
                        v___x_5852_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(v___x_5851_, v_value_5830_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_);
                        if crate::leanh::lean_obj_tag(v___x_5852_) == 0 {
                            v_a_5853_ = crate::leanh::lean_ctor_get(v___x_5852_, 0);
                            v_isSharedCheck_5866_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5852_)) as u8;
                            if v_isSharedCheck_5866_ == 0 {
                                v___x_5855_ = v___x_5852_;
                                v_isShared_5856_ = v_isSharedCheck_5866_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5853_);
                                crate::leanh::lean_dec(v___x_5852_);
                                v___x_5855_ = crate::leanh::lean_box(0);
                                v_isShared_5856_ = v_isSharedCheck_5866_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5849_);
                            crate::leanh::lean_dec(v_a_5845_);
                            crate::leanh::lean_del_object(v___x_5842_);
                            crate::leanh::lean_dec(v_levelParams_5837_);
                            crate::leanh::lean_dec(v_name_5836_);
                            crate::leanh::lean_del_object(v___x_5834_);
                            crate::leanh::lean_dec(v_inlineAttr_x3f_5832_);
                            v_a_5867_ = crate::leanh::lean_ctor_get(v___x_5852_, 0);
                            v_isSharedCheck_5874_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5852_)) as u8;
                            if v_isSharedCheck_5874_ == 0 {
                                v___x_5869_ = v___x_5852_;
                                v_isShared_5870_ = v_isSharedCheck_5874_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5867_);
                                crate::leanh::lean_dec(v___x_5852_);
                                v___x_5869_ = crate::leanh::lean_box(0);
                                v_isShared_5870_ = v_isSharedCheck_5874_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5845_);
                        crate::leanh::lean_del_object(v___x_5842_);
                        crate::leanh::lean_dec(v_levelParams_5837_);
                        crate::leanh::lean_dec(v_name_5836_);
                        crate::leanh::lean_del_object(v___x_5834_);
                        crate::leanh::lean_dec(v_inlineAttr_x3f_5832_);
                        crate::leanh::lean_dec_ref(v_value_5830_);
                        v_a_5875_ = crate::leanh::lean_ctor_get(v___x_5848_, 0);
                        v_isSharedCheck_5882_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5848_)) as u8;
                        if v_isSharedCheck_5882_ == 0 {
                            v___x_5877_ = v___x_5848_;
                            v_isShared_5878_ = v_isSharedCheck_5882_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5875_);
                            crate::leanh::lean_dec(v___x_5848_);
                            v___x_5877_ = crate::leanh::lean_box(0);
                            v_isShared_5878_ = v_isSharedCheck_5882_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5842_);
                    crate::leanh::lean_dec_ref(v_params_5839_);
                    crate::leanh::lean_dec(v_levelParams_5837_);
                    crate::leanh::lean_dec(v_name_5836_);
                    crate::leanh::lean_del_object(v___x_5834_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_5832_);
                    crate::leanh::lean_dec_ref(v_value_5830_);
                    v_a_5883_ = crate::leanh::lean_ctor_get(v___x_5844_, 0);
                    v_isSharedCheck_5890_ = (!crate::leanh::lean_is_exclusive(v___x_5844_)) as u8;
                    if v_isSharedCheck_5890_ == 0 {
                        v___x_5885_ = v___x_5844_;
                        v_isShared_5886_ = v_isSharedCheck_5890_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5883_);
                        crate::leanh::lean_dec(v___x_5844_);
                        v___x_5885_ = crate::leanh::lean_box(0);
                        v_isShared_5886_ = v_isSharedCheck_5890_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5842_, 3, v_a_5849_);
                    crate::leanh::lean_ctor_set(v___x_5842_, 2, v_a_5845_);
                    v___x_5858_ = v___x_5842_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5865_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_name_5836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5865_, 1, v_levelParams_5837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5865_, 2, v_a_5845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5865_, 3, v_a_5849_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5865_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_safe_5840_,
                    );
                    v___x_5858_ = v_reuseFailAlloc_5865_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5834_, 1, v_a_5853_);
                    crate::leanh::lean_ctor_set(v___x_5834_, 0, v___x_5858_);
                    v___x_5860_ = v___x_5834_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5864_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5864_, 0, v___x_5858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5864_, 1, v_a_5853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5864_, 2, v_inlineAttr_x3f_5832_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5864_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_5831_,
                    );
                    v___x_5860_ = v_reuseFailAlloc_5864_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5856_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5855_, 0, v___x_5860_);
                    v___x_5862_ = v___x_5855_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5863_, 0, v___x_5860_);
                    v___x_5862_ = v_reuseFailAlloc_5863_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5862_;
            }
            7 => {
                if v_isShared_5870_ == 0 {
                    v___x_5872_ = v___x_5869_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5867_);
                    v___x_5872_ = v_reuseFailAlloc_5873_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5872_;
            }
            9 => {
                if v_isShared_5878_ == 0 {
                    v___x_5880_ = v___x_5877_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_a_5875_);
                    v___x_5880_ = v_reuseFailAlloc_5881_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5880_;
            }
            11 => {
                if v_isShared_5886_ == 0 {
                    v___x_5888_ = v___x_5885_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5889_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_a_5883_);
                    v___x_5888_ = v_reuseFailAlloc_5889_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(
    mut v_pu_5893_: *mut crate::leanh::LeanObject,
    mut v_decl_5894_: *mut crate::leanh::LeanObject,
    mut v_a_5895_: *mut crate::leanh::LeanObject,
    mut v_a_5896_: *mut crate::leanh::LeanObject,
    mut v_a_5897_: *mut crate::leanh::LeanObject,
    mut v_a_5898_: *mut crate::leanh::LeanObject,
    mut v_a_5899_: *mut crate::leanh::LeanObject,
    mut v_a_5900_: *mut crate::leanh::LeanObject,
    mut v_a_5901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5902_: u8 = 0;
    let mut v_a_boxed_5903_: u8 = 0;
    let mut v_res_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5902_ = (crate::leanh::lean_unbox(v_pu_5893_) as u8);
    v_a_boxed_5903_ = (crate::leanh::lean_unbox(v_a_5895_) as u8);
    v_res_5904_ =
        l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(
            v_pu_boxed_5902_,
            v_decl_5894_,
            v_a_boxed_5903_,
            v_a_5896_,
            v_a_5897_,
            v_a_5898_,
            v_a_5899_,
            v_a_5900_,
        );
    crate::leanh::lean_dec(v_a_5900_);
    crate::leanh::lean_dec_ref(v_a_5899_);
    crate::leanh::lean_dec(v_a_5898_);
    crate::leanh::lean_dec_ref(v_a_5897_);
    crate::leanh::lean_dec(v_a_5896_);
    return v_res_5904_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_internalize(
    mut v_pu_5905_: u8,
    mut v_decl_5906_: *mut crate::leanh::LeanObject,
    mut v_s_5907_: *mut crate::leanh::LeanObject,
    mut v_uniqueIdents_5908_: u8,
    mut v_a_5909_: *mut crate::leanh::LeanObject,
    mut v_a_5910_: *mut crate::leanh::LeanObject,
    mut v_a_5911_: *mut crate::leanh::LeanObject,
    mut v_a_5912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5919_: u8 = 0;
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5914_ = lean_st_mk_ref(v_s_5907_);
                v___x_5915_ = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(v_pu_5905_, v_decl_5906_, v_uniqueIdents_5908_, v___x_5914_, v_a_5909_, v_a_5910_, v_a_5911_, v_a_5912_);
                if crate::leanh::lean_obj_tag(v___x_5915_) == 0 {
                    v_a_5916_ = crate::leanh::lean_ctor_get(v___x_5915_, 0);
                    v_isSharedCheck_5924_ = (!crate::leanh::lean_is_exclusive(v___x_5915_)) as u8;
                    if v_isSharedCheck_5924_ == 0 {
                        v___x_5918_ = v___x_5915_;
                        v_isShared_5919_ = v_isSharedCheck_5924_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5916_);
                        crate::leanh::lean_dec(v___x_5915_);
                        v___x_5918_ = crate::leanh::lean_box(0);
                        v_isShared_5919_ = v_isSharedCheck_5924_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5914_);
                    return v___x_5915_;
                }
            }
            1 => {
                v___x_5920_ = lean_st_ref_get(v___x_5914_);
                crate::leanh::lean_dec(v___x_5914_);
                crate::leanh::lean_dec(v___x_5920_);
                if v_isShared_5919_ == 0 {
                    v___x_5922_ = v___x_5918_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_a_5916_);
                    v___x_5922_ = v_reuseFailAlloc_5923_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_internalize___boxed(
    mut v_pu_5925_: *mut crate::leanh::LeanObject,
    mut v_decl_5926_: *mut crate::leanh::LeanObject,
    mut v_s_5927_: *mut crate::leanh::LeanObject,
    mut v_uniqueIdents_5928_: *mut crate::leanh::LeanObject,
    mut v_a_5929_: *mut crate::leanh::LeanObject,
    mut v_a_5930_: *mut crate::leanh::LeanObject,
    mut v_a_5931_: *mut crate::leanh::LeanObject,
    mut v_a_5932_: *mut crate::leanh::LeanObject,
    mut v_a_5933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5934_: u8 = 0;
    let mut v_uniqueIdents_boxed_5935_: u8 = 0;
    let mut v_res_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5934_ = (crate::leanh::lean_unbox(v_pu_5925_) as u8);
    v_uniqueIdents_boxed_5935_ = (crate::leanh::lean_unbox(v_uniqueIdents_5928_) as u8);
    v_res_5936_ = l_Lean_Compiler_LCNF_Decl_internalize(
        v_pu_boxed_5934_,
        v_decl_5926_,
        v_s_5927_,
        v_uniqueIdents_boxed_5935_,
        v_a_5929_,
        v_a_5930_,
        v_a_5931_,
        v_a_5932_,
    );
    crate::leanh::lean_dec(v_a_5932_);
    crate::leanh::lean_dec_ref(v_a_5931_);
    crate::leanh::lean_dec(v_a_5930_);
    crate::leanh::lean_dec_ref(v_a_5929_);
    return v_res_5936_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5937_ = crate::leanh::lean_box(0);
    v___x_5938_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5939_ = lean_mk_array(v___x_5938_, v___x_5937_);
    return v___x_5939_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5940_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
    v___x_5941_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5942_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5942_, 0, v___x_5941_);
    crate::leanh::lean_ctor_set(v___x_5942_, 1, v___x_5940_);
    return v___x_5942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(
    mut v_pu_5943_: u8,
    mut v_sz_5944_: usize,
    mut v_i_5945_: usize,
    mut v_bs_5946_: *mut crate::leanh::LeanObject,
    mut v___y_5947_: *mut crate::leanh::LeanObject,
    mut v___y_5948_: *mut crate::leanh::LeanObject,
    mut v___y_5949_: *mut crate::leanh::LeanObject,
    mut v___y_5950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5952_: u8 = 0;
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5958_: u8 = 0;
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: u8 = 0;
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: usize = 0;
    let mut v___x_5971_: usize = 0;
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5977_: u8 = 0;
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut v_reuseFailAlloc_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5983_: u8 = 0;
    let mut v_unused_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5952_ = lean_usize_dec_lt(v_i_5945_, v_sz_5944_);
                if v___x_5952_ == 0 {
                    v___x_5953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5953_, 0, v_bs_5946_);
                    return v___x_5953_;
                } else {
                    v___x_5954_ = lean_st_ref_take(v___y_5948_);
                    v_lctx_5955_ = crate::leanh::lean_ctor_get(v___x_5954_, 0);
                    v_isSharedCheck_5983_ = (!crate::leanh::lean_is_exclusive(v___x_5954_)) as u8;
                    if v_isSharedCheck_5983_ == 0 {
                        v_unused_5984_ = crate::leanh::lean_ctor_get(v___x_5954_, 1);
                        crate::leanh::lean_dec(v_unused_5984_);
                        v___x_5957_ = v___x_5954_;
                        v_isShared_5958_ = v_isSharedCheck_5983_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_lctx_5955_);
                        crate::leanh::lean_dec(v___x_5954_);
                        v___x_5957_ = crate::leanh::lean_box(0);
                        v_isShared_5958_ = v_isSharedCheck_5983_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5959_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_5958_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5957_, 1, v___x_5959_);
                    v___x_5961_ = v___x_5957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5982_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_lctx_5955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5982_, 1, v___x_5959_);
                    v___x_5961_ = v_reuseFailAlloc_5982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5962_ = lean_st_ref_set(v___y_5948_, v___x_5961_);
                v_v_5963_ = lean_array_uget_borrowed(v_bs_5946_, v_i_5945_);
                v___x_5964_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5965_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
                v___x_5966_ = 0;
                crate::leanh::lean_inc(v_v_5963_);
                v___x_5967_ = l_Lean_Compiler_LCNF_Decl_internalize(
                    v_pu_5943_,
                    v_v_5963_,
                    v___x_5965_,
                    v___x_5966_,
                    v___y_5947_,
                    v___y_5948_,
                    v___y_5949_,
                    v___y_5950_,
                );
                if crate::leanh::lean_obj_tag(v___x_5967_) == 0 {
                    v_a_5968_ = crate::leanh::lean_ctor_get(v___x_5967_, 0);
                    crate::leanh::lean_inc(v_a_5968_);
                    crate::leanh::lean_dec_ref_known(v___x_5967_, 1);
                    v_bs_x27_5969_ = lean_array_uset(v_bs_5946_, v_i_5945_, v___x_5964_);
                    v___x_5970_ = 1usize;
                    v___x_5971_ = lean_usize_add(v_i_5945_, v___x_5970_);
                    v___x_5972_ = lean_array_uset(v_bs_x27_5969_, v_i_5945_, v_a_5968_);
                    v_i_5945_ = v___x_5971_;
                    v_bs_5946_ = v___x_5972_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_5946_);
                    v_a_5974_ = crate::leanh::lean_ctor_get(v___x_5967_, 0);
                    v_isSharedCheck_5981_ = (!crate::leanh::lean_is_exclusive(v___x_5967_)) as u8;
                    if v_isSharedCheck_5981_ == 0 {
                        v___x_5976_ = v___x_5967_;
                        v_isShared_5977_ = v_isSharedCheck_5981_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5974_);
                        crate::leanh::lean_dec(v___x_5967_);
                        v___x_5976_ = crate::leanh::lean_box(0);
                        v_isShared_5977_ = v_isSharedCheck_5981_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5977_ == 0 {
                    v___x_5979_ = v___x_5976_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5980_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
                    v___x_5979_ = v_reuseFailAlloc_5980_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(
    mut v_pu_5985_: *mut crate::leanh::LeanObject,
    mut v_sz_5986_: *mut crate::leanh::LeanObject,
    mut v_i_5987_: *mut crate::leanh::LeanObject,
    mut v_bs_5988_: *mut crate::leanh::LeanObject,
    mut v___y_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
    mut v___y_5991_: *mut crate::leanh::LeanObject,
    mut v___y_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5994_: u8 = 0;
    let mut v_sz_boxed_5995_: usize = 0;
    let mut v_i_boxed_5996_: usize = 0;
    let mut v_res_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5994_ = (crate::leanh::lean_unbox(v_pu_5985_) as u8);
    v_sz_boxed_5995_ = crate::leanh::lean_unbox_usize(v_sz_5986_);
    crate::leanh::lean_dec(v_sz_5986_);
    v_i_boxed_5996_ = crate::leanh::lean_unbox_usize(v_i_5987_);
    crate::leanh::lean_dec(v_i_5987_);
    v_res_5997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_boxed_5994_, v_sz_boxed_5995_, v_i_boxed_5996_, v_bs_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_);
    crate::leanh::lean_dec(v___y_5992_);
    crate::leanh::lean_dec_ref(v___y_5991_);
    crate::leanh::lean_dec(v___y_5990_);
    crate::leanh::lean_dec_ref(v___y_5989_);
    return v_res_5997_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_cleanup___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5998_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
    v___x_5999_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5999_, 0, v___x_5998_);
    crate::leanh::lean_ctor_set(v___x_5999_, 1, v___x_5998_);
    crate::leanh::lean_ctor_set(v___x_5999_, 2, v___x_5998_);
    crate::leanh::lean_ctor_set(v___x_5999_, 3, v___x_5998_);
    crate::leanh::lean_ctor_set(v___x_5999_, 4, v___x_5998_);
    crate::leanh::lean_ctor_set(v___x_5999_, 5, v___x_5998_);
    return v___x_5999_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_cleanup___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6000_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_6001_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_cleanup___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_cleanup___closed__0_once),
        _init_l_Lean_Compiler_LCNF_cleanup___closed__0,
    );
    v___x_6002_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6002_, 0, v___x_6001_);
    crate::leanh::lean_ctor_set(v___x_6002_, 1, v___x_6000_);
    return v___x_6002_;
}
pub unsafe fn l_Lean_Compiler_LCNF_cleanup(
    mut v_pu_6003_: u8,
    mut v_decl_6004_: *mut crate::leanh::LeanObject,
    mut v_a_6005_: *mut crate::leanh::LeanObject,
    mut v_a_6006_: *mut crate::leanh::LeanObject,
    mut v_a_6007_: *mut crate::leanh::LeanObject,
    mut v_a_6008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6013_: usize = 0;
    let mut v___x_6014_: usize = 0;
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6010_ = lean_st_ref_take(v_a_6006_);
    crate::leanh::lean_dec(v___x_6010_);
    v___x_6011_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_cleanup___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_cleanup___closed__1_once),
        _init_l_Lean_Compiler_LCNF_cleanup___closed__1,
    );
    v___x_6012_ = lean_st_ref_set(v_a_6006_, v___x_6011_);
    v_sz_6013_ = lean_array_size(v_decl_6004_);
    v___x_6014_ = 0usize;
    v___x_6015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(v_pu_6003_, v_sz_6013_, v___x_6014_, v_decl_6004_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_);
    return v___x_6015_;
}
pub unsafe fn l_Lean_Compiler_LCNF_cleanup___boxed(
    mut v_pu_6016_: *mut crate::leanh::LeanObject,
    mut v_decl_6017_: *mut crate::leanh::LeanObject,
    mut v_a_6018_: *mut crate::leanh::LeanObject,
    mut v_a_6019_: *mut crate::leanh::LeanObject,
    mut v_a_6020_: *mut crate::leanh::LeanObject,
    mut v_a_6021_: *mut crate::leanh::LeanObject,
    mut v_a_6022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6023_: u8 = 0;
    let mut v_res_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6023_ = (crate::leanh::lean_unbox(v_pu_6016_) as u8);
    v_res_6024_ = l_Lean_Compiler_LCNF_cleanup(
        v_pu_boxed_6023_,
        v_decl_6017_,
        v_a_6018_,
        v_a_6019_,
        v_a_6020_,
        v_a_6021_,
    );
    crate::leanh::lean_dec(v_a_6021_);
    crate::leanh::lean_dec_ref(v_a_6020_);
    crate::leanh::lean_dec(v_a_6019_);
    crate::leanh::lean_dec_ref(v_a_6018_);
    return v_res_6024_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(
    mut v_a_6025_: *mut crate::leanh::LeanObject,
    mut v_ngen_6026_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_6027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6047_: u8 = 0;
    let mut v_unused_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6029_ = lean_st_ref_take(v_a_6025_);
                v_env_6030_ = crate::leanh::lean_ctor_get(v___x_6029_, 0);
                v_nextMacroScope_6031_ = crate::leanh::lean_ctor_get(v___x_6029_, 1);
                v_auxDeclNGen_6032_ = crate::leanh::lean_ctor_get(v___x_6029_, 3);
                v_traceState_6033_ = crate::leanh::lean_ctor_get(v___x_6029_, 4);
                v_cache_6034_ = crate::leanh::lean_ctor_get(v___x_6029_, 5);
                v_messages_6035_ = crate::leanh::lean_ctor_get(v___x_6029_, 6);
                v_infoState_6036_ = crate::leanh::lean_ctor_get(v___x_6029_, 7);
                v_snapshotTasks_6037_ = crate::leanh::lean_ctor_get(v___x_6029_, 8);
                v_isSharedCheck_6047_ = (!crate::leanh::lean_is_exclusive(v___x_6029_)) as u8;
                if v_isSharedCheck_6047_ == 0 {
                    v_unused_6048_ = crate::leanh::lean_ctor_get(v___x_6029_, 2);
                    crate::leanh::lean_dec(v_unused_6048_);
                    v___x_6039_ = v___x_6029_;
                    v_isShared_6040_ = v_isSharedCheck_6047_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6037_);
                    crate::leanh::lean_inc(v_infoState_6036_);
                    crate::leanh::lean_inc(v_messages_6035_);
                    crate::leanh::lean_inc(v_cache_6034_);
                    crate::leanh::lean_inc(v_traceState_6033_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6032_);
                    crate::leanh::lean_inc(v_nextMacroScope_6031_);
                    crate::leanh::lean_inc(v_env_6030_);
                    crate::leanh::lean_dec(v___x_6029_);
                    v___x_6039_ = crate::leanh::lean_box(0);
                    v_isShared_6040_ = v_isSharedCheck_6047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_6040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6039_, 2, v_ngen_6026_);
                    v___x_6042_ = v___x_6039_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6046_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 0, v_env_6030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 1, v_nextMacroScope_6031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 2, v_ngen_6026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 3, v_auxDeclNGen_6032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 4, v_traceState_6033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 5, v_cache_6034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 6, v_messages_6035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 7, v_infoState_6036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 8, v_snapshotTasks_6037_);
                    v___x_6042_ = v_reuseFailAlloc_6046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6043_ = lean_st_ref_set(v_a_6025_, v___x_6042_);
                v___x_6044_ = crate::leanh::lean_box(0);
                v___x_6045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6045_, 0, v___x_6044_);
                return v___x_6045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(
    mut v_a_6049_: *mut crate::leanh::LeanObject,
    mut v_ngen_6050_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_6051_: *mut crate::leanh::LeanObject,
    mut v___y_6052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6053_ =
        l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(v_a_6049_, v_ngen_6050_, v_a_x3f_6051_);
    crate::leanh::lean_dec(v_a_x3f_6051_);
    crate::leanh::lean_dec(v_a_6049_);
    return v_res_6053_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normalizeFVarIds(
    mut v_pu_6060_: u8,
    mut v_decl_6061_: *mut crate::leanh::LeanObject,
    mut v_a_6062_: *mut crate::leanh::LeanObject,
    mut v_a_6063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: u8 = 0;
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: u8 = 0;
    let mut v_r_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6094_: u8 = 0;
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6100_: u8 = 0;
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6104_: u8 = 0;
    let mut v_unused_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6107_: u8 = 0;
    let mut v_a_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6113_: u8 = 0;
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6117_: u8 = 0;
    let mut v_unused_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6120_: u8 = 0;
    let mut v_unused_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6065_ = lean_st_ref_get(v_a_6063_);
                v___x_6066_ = lean_st_ref_take(v_a_6063_);
                v_env_6067_ = crate::leanh::lean_ctor_get(v___x_6066_, 0);
                v_nextMacroScope_6068_ = crate::leanh::lean_ctor_get(v___x_6066_, 1);
                v_auxDeclNGen_6069_ = crate::leanh::lean_ctor_get(v___x_6066_, 3);
                v_traceState_6070_ = crate::leanh::lean_ctor_get(v___x_6066_, 4);
                v_cache_6071_ = crate::leanh::lean_ctor_get(v___x_6066_, 5);
                v_messages_6072_ = crate::leanh::lean_ctor_get(v___x_6066_, 6);
                v_infoState_6073_ = crate::leanh::lean_ctor_get(v___x_6066_, 7);
                v_snapshotTasks_6074_ = crate::leanh::lean_ctor_get(v___x_6066_, 8);
                v_isSharedCheck_6120_ = (!crate::leanh::lean_is_exclusive(v___x_6066_)) as u8;
                if v_isSharedCheck_6120_ == 0 {
                    v_unused_6121_ = crate::leanh::lean_ctor_get(v___x_6066_, 2);
                    crate::leanh::lean_dec(v_unused_6121_);
                    v___x_6076_ = v___x_6066_;
                    v_isShared_6077_ = v_isSharedCheck_6120_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6074_);
                    crate::leanh::lean_inc(v_infoState_6073_);
                    crate::leanh::lean_inc(v_messages_6072_);
                    crate::leanh::lean_inc(v_cache_6071_);
                    crate::leanh::lean_inc(v_traceState_6070_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6069_);
                    crate::leanh::lean_inc(v_nextMacroScope_6068_);
                    crate::leanh::lean_inc(v_env_6067_);
                    crate::leanh::lean_dec(v___x_6066_);
                    v___x_6076_ = crate::leanh::lean_box(0);
                    v_isShared_6077_ = v_isSharedCheck_6120_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6078_ = l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2;
                if v_isShared_6077_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6076_, 2, v___x_6078_);
                    v___x_6080_ = v___x_6076_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6119_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_env_6067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 1, v_nextMacroScope_6068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 2, v___x_6078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 3, v_auxDeclNGen_6069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 4, v_traceState_6070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 5, v_cache_6071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 6, v_messages_6072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 7, v_infoState_6073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 8, v_snapshotTasks_6074_);
                    v___x_6080_ = v_reuseFailAlloc_6119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6081_ = lean_st_ref_set(v_a_6063_, v___x_6080_);
                v_ngen_6082_ = crate::leanh::lean_ctor_get(v___x_6065_, 2);
                crate::leanh::lean_inc_ref(v_ngen_6082_);
                crate::leanh::lean_dec(v___x_6065_);
                v___x_6083_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
                v___x_6084_ = 0;
                v___x_6085_ = crate::leanh::lean_box((v_pu_6060_) as usize);
                v___x_6086_ = crate::leanh::lean_box((v___x_6084_) as usize);
                v___x_6087_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Decl_internalize___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_6087_, 0, v___x_6085_);
                crate::leanh::lean_closure_set(v___x_6087_, 1, v_decl_6061_);
                crate::leanh::lean_closure_set(v___x_6087_, 2, v___x_6083_);
                crate::leanh::lean_closure_set(v___x_6087_, 3, v___x_6086_);
                v___x_6088_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_cleanup___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_cleanup___closed__1_once),
                    _init_l_Lean_Compiler_LCNF_cleanup___closed__1,
                );
                v___x_6089_ = 0;
                v_r_6090_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(
                    v___x_6087_,
                    v___x_6088_,
                    v___x_6089_,
                    v_a_6062_,
                    v_a_6063_,
                );
                if crate::leanh::lean_obj_tag(v_r_6090_) == 0 {
                    v_a_6091_ = crate::leanh::lean_ctor_get(v_r_6090_, 0);
                    v_isSharedCheck_6107_ = (!crate::leanh::lean_is_exclusive(v_r_6090_)) as u8;
                    if v_isSharedCheck_6107_ == 0 {
                        v___x_6093_ = v_r_6090_;
                        v_isShared_6094_ = v_isSharedCheck_6107_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6091_);
                        crate::leanh::lean_dec(v_r_6090_);
                        v___x_6093_ = crate::leanh::lean_box(0);
                        v_isShared_6094_ = v_isSharedCheck_6107_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_6108_ = crate::leanh::lean_ctor_get(v_r_6090_, 0);
                    crate::leanh::lean_inc(v_a_6108_);
                    crate::leanh::lean_dec_ref_known(v_r_6090_, 1);
                    v___x_6109_ = crate::leanh::lean_box(0);
                    v___x_6110_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(
                        v_a_6063_,
                        v_ngen_6082_,
                        v___x_6109_,
                    );
                    v_isSharedCheck_6117_ = (!crate::leanh::lean_is_exclusive(v___x_6110_)) as u8;
                    if v_isSharedCheck_6117_ == 0 {
                        v_unused_6118_ = crate::leanh::lean_ctor_get(v___x_6110_, 0);
                        crate::leanh::lean_dec(v_unused_6118_);
                        v___x_6112_ = v___x_6110_;
                        v_isShared_6113_ = v_isSharedCheck_6117_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6110_);
                        v___x_6112_ = crate::leanh::lean_box(0);
                        v_isShared_6113_ = v_isSharedCheck_6117_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_6091_);
                if v_isShared_6094_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6093_, 1);
                    v___x_6096_ = v___x_6093_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6106_, 0, v_a_6091_);
                    v___x_6096_ = v_reuseFailAlloc_6106_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6097_ = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(
                    v_a_6063_,
                    v_ngen_6082_,
                    v___x_6096_,
                );
                crate::leanh::lean_dec_ref(v___x_6096_);
                v_isSharedCheck_6104_ = (!crate::leanh::lean_is_exclusive(v___x_6097_)) as u8;
                if v_isSharedCheck_6104_ == 0 {
                    v_unused_6105_ = crate::leanh::lean_ctor_get(v___x_6097_, 0);
                    crate::leanh::lean_dec(v_unused_6105_);
                    v___x_6099_ = v___x_6097_;
                    v_isShared_6100_ = v_isSharedCheck_6104_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_6097_);
                    v___x_6099_ = crate::leanh::lean_box(0);
                    v_isShared_6100_ = v_isSharedCheck_6104_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6100_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6099_, 0, v_a_6091_);
                    v___x_6102_ = v___x_6099_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6103_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6103_, 0, v_a_6091_);
                    v___x_6102_ = v_reuseFailAlloc_6103_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6102_;
            }
            7 => {
                if v_isShared_6113_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6112_, 1);
                    crate::leanh::lean_ctor_set(v___x_6112_, 0, v_a_6108_);
                    v___x_6115_ = v___x_6112_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_a_6108_);
                    v___x_6115_ = v_reuseFailAlloc_6116_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(
    mut v_pu_6122_: *mut crate::leanh::LeanObject,
    mut v_decl_6123_: *mut crate::leanh::LeanObject,
    mut v_a_6124_: *mut crate::leanh::LeanObject,
    mut v_a_6125_: *mut crate::leanh::LeanObject,
    mut v_a_6126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6127_: u8 = 0;
    let mut v_res_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6127_ = (crate::leanh::lean_unbox(v_pu_6122_) as u8);
    v_res_6128_ =
        l_Lean_Compiler_LCNF_normalizeFVarIds(v_pu_boxed_6127_, v_decl_6123_, v_a_6124_, v_a_6125_);
    crate::leanh::lean_dec(v_a_6125_);
    crate::leanh::lean_dec_ref(v_a_6124_);
    return v_res_6128_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Internalize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Bind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Internalize(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Internalize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Bind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Internalize(builtin);
}
