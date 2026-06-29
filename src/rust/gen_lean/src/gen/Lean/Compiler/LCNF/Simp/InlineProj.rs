// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.InlineProj
// Imports: Lean.Compiler.LCNF.Simp.SimpM
use crate::r#gen::Init::Control::Option::l_OptionT_instInhabitedOfPure___redArg;
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams,
    l_Lean_Compiler_LCNF_Decl_getArity___redArg,
    l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_Phase_toPurity, l_Lean_Compiler_LCNF_eraseCode___redArg,
    l_Lean_Compiler_LCNF_eraseCodeDecls, l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg,
    l_Lean_Compiler_LCNF_getPhase___redArg, l_Lean_Compiler_LCNF_getType,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, l_Lean_Compiler_LCNF_mkLetDeclErased,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::l_Lean_Compiler_LCNF_LetValue_inferType;
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::l_Lean_Compiler_LCNF_getDeclAt_x3f;
use crate::r#gen::Lean::Compiler::LCNF::Simp::SimpM::{
    initialize_Lean_Compiler_LCNF_Simp_SimpM, l_Lean_Compiler_LCNF_Simp_betaReduce,
    l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed,
    l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed,
    runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Compiler_LCNF_isClass_x3f___redArg;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq,
    lean_panic_fn_borrowed,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed as *const core::ffi::c_void, m_arity: 10, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1_value: crate::leanh::LeanStringObject<92> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 73, 110, 108, 105, 110, 101, 80, 114, 111, 106, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 105, 110, 108, 105, 110, 101, 80, 114, 111, 106, 73, 110, 115, 116, 63, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 73, 110, 108, 105, 110, 101, 80, 114, 111, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_506_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(
    mut v_msg_513_: *mut crate::leanh::LeanObject,
    mut v___y_514_: *mut crate::leanh::LeanObject,
    mut v___y_515_: *mut crate::leanh::LeanObject,
    mut v___y_516_: *mut crate::leanh::LeanObject,
    mut v___y_517_: *mut crate::leanh::LeanObject,
    mut v___y_518_: *mut crate::leanh::LeanObject,
    mut v___y_519_: *mut crate::leanh::LeanObject,
    mut v___y_520_: *mut crate::leanh::LeanObject,
    mut v___y_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_528_: u8 = 0;
    let mut v_toFunctor_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_535_: u8 = 0;
    let mut v___f_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_552_: u8 = 0;
    let mut v_toFunctor_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_559_: u8 = 0;
    let mut v___f_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_577_: u8 = 0;
    let mut v_toFunctor_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___f_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_24001__overap_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut v_unused_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_607_: u8 = 0;
    let mut v_unused_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v_unused_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_613_: u8 = 0;
    let mut v_unused_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut v_unused_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_unused_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_523_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0);
                v___x_524_ = l_StateRefT_x27_instMonad___redArg(v___x_523_);
                v_toApplicative_525_ = crate::leanh::lean_ctor_get(v___x_524_, 0);
                v_isSharedCheck_619_ = (!crate::leanh::lean_is_exclusive(v___x_524_)) as u8;
                if v_isSharedCheck_619_ == 0 {
                    v_unused_620_ = crate::leanh::lean_ctor_get(v___x_524_, 1);
                    crate::leanh::lean_dec(v_unused_620_);
                    v___x_527_ = v___x_524_;
                    v_isShared_528_ = v_isSharedCheck_619_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_525_);
                    crate::leanh::lean_dec(v___x_524_);
                    v___x_527_ = crate::leanh::lean_box(0);
                    v_isShared_528_ = v_isSharedCheck_619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_529_ = crate::leanh::lean_ctor_get(v_toApplicative_525_, 0);
                v_toSeq_530_ = crate::leanh::lean_ctor_get(v_toApplicative_525_, 2);
                v_toSeqLeft_531_ = crate::leanh::lean_ctor_get(v_toApplicative_525_, 3);
                v_toSeqRight_532_ = crate::leanh::lean_ctor_get(v_toApplicative_525_, 4);
                v_isSharedCheck_617_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_525_)) as u8;
                if v_isSharedCheck_617_ == 0 {
                    v_unused_618_ = crate::leanh::lean_ctor_get(v_toApplicative_525_, 1);
                    crate::leanh::lean_dec(v_unused_618_);
                    v___x_534_ = v_toApplicative_525_;
                    v_isShared_535_ = v_isSharedCheck_617_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_532_);
                    crate::leanh::lean_inc(v_toSeqLeft_531_);
                    crate::leanh::lean_inc(v_toSeq_530_);
                    crate::leanh::lean_inc(v_toFunctor_529_);
                    crate::leanh::lean_dec(v_toApplicative_525_);
                    v___x_534_ = crate::leanh::lean_box(0);
                    v_isShared_535_ = v_isSharedCheck_617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_536_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1;
                v___f_537_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_529_);
                v___f_538_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_538_, 0, v_toFunctor_529_);
                v___f_539_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_539_, 0, v_toFunctor_529_);
                v___x_540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_540_, 0, v___f_538_);
                crate::leanh::lean_ctor_set(v___x_540_, 1, v___f_539_);
                v___f_541_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_541_, 0, v_toSeqRight_532_);
                v___f_542_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_542_, 0, v_toSeqLeft_531_);
                v___f_543_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_543_, 0, v_toSeq_530_);
                if v_isShared_535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_534_, 4, v___f_541_);
                    crate::leanh::lean_ctor_set(v___x_534_, 3, v___f_542_);
                    crate::leanh::lean_ctor_set(v___x_534_, 2, v___f_543_);
                    crate::leanh::lean_ctor_set(v___x_534_, 1, v___f_536_);
                    crate::leanh::lean_ctor_set(v___x_534_, 0, v___x_540_);
                    v___x_545_ = v___x_534_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_616_, 1, v___f_536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_616_, 2, v___f_543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_616_, 3, v___f_542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_616_, 4, v___f_541_);
                    v___x_545_ = v_reuseFailAlloc_616_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_528_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_527_, 1, v___f_537_);
                    crate::leanh::lean_ctor_set(v___x_527_, 0, v___x_545_);
                    v___x_547_ = v___x_527_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_615_, 1, v___f_537_);
                    v___x_547_ = v_reuseFailAlloc_615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_548_ = l_StateRefT_x27_instMonad___redArg(v___x_547_);
                v_toApplicative_549_ = crate::leanh::lean_ctor_get(v___x_548_, 0);
                v_isSharedCheck_613_ = (!crate::leanh::lean_is_exclusive(v___x_548_)) as u8;
                if v_isSharedCheck_613_ == 0 {
                    v_unused_614_ = crate::leanh::lean_ctor_get(v___x_548_, 1);
                    crate::leanh::lean_dec(v_unused_614_);
                    v___x_551_ = v___x_548_;
                    v_isShared_552_ = v_isSharedCheck_613_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_549_);
                    crate::leanh::lean_dec(v___x_548_);
                    v___x_551_ = crate::leanh::lean_box(0);
                    v_isShared_552_ = v_isSharedCheck_613_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_553_ = crate::leanh::lean_ctor_get(v_toApplicative_549_, 0);
                v_toSeq_554_ = crate::leanh::lean_ctor_get(v_toApplicative_549_, 2);
                v_toSeqLeft_555_ = crate::leanh::lean_ctor_get(v_toApplicative_549_, 3);
                v_toSeqRight_556_ = crate::leanh::lean_ctor_get(v_toApplicative_549_, 4);
                v_isSharedCheck_611_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_549_)) as u8;
                if v_isSharedCheck_611_ == 0 {
                    v_unused_612_ = crate::leanh::lean_ctor_get(v_toApplicative_549_, 1);
                    crate::leanh::lean_dec(v_unused_612_);
                    v___x_558_ = v_toApplicative_549_;
                    v_isShared_559_ = v_isSharedCheck_611_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_556_);
                    crate::leanh::lean_inc(v_toSeqLeft_555_);
                    crate::leanh::lean_inc(v_toSeq_554_);
                    crate::leanh::lean_inc(v_toFunctor_553_);
                    crate::leanh::lean_dec(v_toApplicative_549_);
                    v___x_558_ = crate::leanh::lean_box(0);
                    v_isShared_559_ = v_isSharedCheck_611_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_560_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3;
                v___f_561_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_553_);
                v___f_562_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_562_, 0, v_toFunctor_553_);
                v___f_563_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_563_, 0, v_toFunctor_553_);
                v___x_564_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_564_, 0, v___f_562_);
                crate::leanh::lean_ctor_set(v___x_564_, 1, v___f_563_);
                v___f_565_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_565_, 0, v_toSeqRight_556_);
                v___f_566_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_566_, 0, v_toSeqLeft_555_);
                v___f_567_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_567_, 0, v_toSeq_554_);
                if v_isShared_559_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_558_, 4, v___f_565_);
                    crate::leanh::lean_ctor_set(v___x_558_, 3, v___f_566_);
                    crate::leanh::lean_ctor_set(v___x_558_, 2, v___f_567_);
                    crate::leanh::lean_ctor_set(v___x_558_, 1, v___f_560_);
                    crate::leanh::lean_ctor_set(v___x_558_, 0, v___x_564_);
                    v___x_569_ = v___x_558_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_610_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_610_, 1, v___f_560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_610_, 2, v___f_567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_610_, 3, v___f_566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_610_, 4, v___f_565_);
                    v___x_569_ = v_reuseFailAlloc_610_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_552_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_551_, 1, v___f_561_);
                    crate::leanh::lean_ctor_set(v___x_551_, 0, v___x_569_);
                    v___x_571_ = v___x_551_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_609_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_609_, 1, v___f_561_);
                    v___x_571_ = v_reuseFailAlloc_609_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_572_ = l_ReaderT_instMonad___redArg(v___x_571_);
                v___x_573_ = l_StateRefT_x27_instMonad___redArg(v___x_572_);
                v_toApplicative_574_ = crate::leanh::lean_ctor_get(v___x_573_, 0);
                v_isSharedCheck_607_ = (!crate::leanh::lean_is_exclusive(v___x_573_)) as u8;
                if v_isSharedCheck_607_ == 0 {
                    v_unused_608_ = crate::leanh::lean_ctor_get(v___x_573_, 1);
                    crate::leanh::lean_dec(v_unused_608_);
                    v___x_576_ = v___x_573_;
                    v_isShared_577_ = v_isSharedCheck_607_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_574_);
                    crate::leanh::lean_dec(v___x_573_);
                    v___x_576_ = crate::leanh::lean_box(0);
                    v_isShared_577_ = v_isSharedCheck_607_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_toFunctor_578_ = crate::leanh::lean_ctor_get(v_toApplicative_574_, 0);
                v_toSeq_579_ = crate::leanh::lean_ctor_get(v_toApplicative_574_, 2);
                v_toSeqLeft_580_ = crate::leanh::lean_ctor_get(v_toApplicative_574_, 3);
                v_toSeqRight_581_ = crate::leanh::lean_ctor_get(v_toApplicative_574_, 4);
                v_isSharedCheck_605_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_574_)) as u8;
                if v_isSharedCheck_605_ == 0 {
                    v_unused_606_ = crate::leanh::lean_ctor_get(v_toApplicative_574_, 1);
                    crate::leanh::lean_dec(v_unused_606_);
                    v___x_583_ = v_toApplicative_574_;
                    v_isShared_584_ = v_isSharedCheck_605_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_581_);
                    crate::leanh::lean_inc(v_toSeqLeft_580_);
                    crate::leanh::lean_inc(v_toSeq_579_);
                    crate::leanh::lean_inc(v_toFunctor_578_);
                    crate::leanh::lean_dec(v_toApplicative_574_);
                    v___x_583_ = crate::leanh::lean_box(0);
                    v_isShared_584_ = v_isSharedCheck_605_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___f_585_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5;
                v___f_586_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6;
                crate::leanh::lean_inc_ref(v_toFunctor_578_);
                v___f_587_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_587_, 0, v_toFunctor_578_);
                v___f_588_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_588_, 0, v_toFunctor_578_);
                v___x_589_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_589_, 0, v___f_587_);
                crate::leanh::lean_ctor_set(v___x_589_, 1, v___f_588_);
                v___f_590_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_590_, 0, v_toSeqRight_581_);
                v___f_591_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_591_, 0, v_toSeqLeft_580_);
                v___f_592_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_592_, 0, v_toSeq_579_);
                if v_isShared_584_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_583_, 4, v___f_590_);
                    crate::leanh::lean_ctor_set(v___x_583_, 3, v___f_591_);
                    crate::leanh::lean_ctor_set(v___x_583_, 2, v___f_592_);
                    crate::leanh::lean_ctor_set(v___x_583_, 1, v___f_585_);
                    crate::leanh::lean_ctor_set(v___x_583_, 0, v___x_589_);
                    v___x_594_ = v___x_583_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_604_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 1, v___f_585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 2, v___f_592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 3, v___f_591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 4, v___f_590_);
                    v___x_594_ = v_reuseFailAlloc_604_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_576_, 1, v___f_586_);
                    crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_594_);
                    v___x_596_ = v___x_576_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_603_, 1, v___f_586_);
                    v___x_596_ = v_reuseFailAlloc_603_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_597_ = l_StateRefT_x27_instMonad___redArg(v___x_596_);
                v_toApplicative_598_ = crate::leanh::lean_ctor_get(v___x_597_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_598_);
                crate::leanh::lean_dec_ref(v___x_597_);
                v_toPure_599_ = crate::leanh::lean_ctor_get(v_toApplicative_598_, 1);
                crate::leanh::lean_inc(v_toPure_599_);
                crate::leanh::lean_dec_ref(v_toApplicative_598_);
                v___x_600_ = l_OptionT_instInhabitedOfPure___redArg(v_toPure_599_);
                v___x_24001__overap_601_ = lean_panic_fn_borrowed(v___x_600_, v_msg_513_);
                crate::leanh::lean_dec(v___x_600_);
                crate::leanh::lean_inc(v___y_521_);
                crate::leanh::lean_inc_ref(v___y_520_);
                crate::leanh::lean_inc(v___y_519_);
                crate::leanh::lean_inc_ref(v___y_518_);
                crate::leanh::lean_inc_ref(v___y_517_);
                crate::leanh::lean_inc(v___y_516_);
                crate::leanh::lean_inc_ref(v___y_515_);
                crate::leanh::lean_inc(v___y_514_);
                v___x_602_ = crate::leanh::lean_apply_9(
                    v___x_24001__overap_601_,
                    v___y_514_,
                    v___y_515_,
                    v___y_516_,
                    v___y_517_,
                    v___y_518_,
                    v___y_519_,
                    v___y_520_,
                    v___y_521_,
                    crate::leanh::lean_box(0),
                );
                return v___x_602_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___boxed(
    mut v_msg_621_: *mut crate::leanh::LeanObject,
    mut v___y_622_: *mut crate::leanh::LeanObject,
    mut v___y_623_: *mut crate::leanh::LeanObject,
    mut v___y_624_: *mut crate::leanh::LeanObject,
    mut v___y_625_: *mut crate::leanh::LeanObject,
    mut v___y_626_: *mut crate::leanh::LeanObject,
    mut v___y_627_: *mut crate::leanh::LeanObject,
    mut v___y_628_: *mut crate::leanh::LeanObject,
    mut v___y_629_: *mut crate::leanh::LeanObject,
    mut v___y_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_631_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v_msg_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
    crate::leanh::lean_dec(v___y_629_);
    crate::leanh::lean_dec_ref(v___y_628_);
    crate::leanh::lean_dec(v___y_627_);
    crate::leanh::lean_dec_ref(v___y_626_);
    crate::leanh::lean_dec_ref(v___y_625_);
    crate::leanh::lean_dec(v___y_624_);
    crate::leanh::lean_dec_ref(v___y_623_);
    crate::leanh::lean_dec(v___y_622_);
    return v_res_631_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_635_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2;
    v___x_636_ = crate::leanh::lean_unsigned_to_nat(34);
    v___x_637_ = crate::leanh::lean_unsigned_to_nat(62);
    v___x_638_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1;
    v___x_639_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0;
    v___x_640_ =
        l_mkPanicMessageWithDecl(v___x_639_, v___x_638_, v___x_637_, v___x_636_, v___x_635_);
    return v___x_640_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(
    mut v_fvarId_641_: *mut crate::leanh::LeanObject,
    mut v_projs_642_: *mut crate::leanh::LeanObject,
    mut v_a_643_: *mut crate::leanh::LeanObject,
    mut v_a_644_: *mut crate::leanh::LeanObject,
    mut v_a_645_: *mut crate::leanh::LeanObject,
    mut v_a_646_: *mut crate::leanh::LeanObject,
    mut v_a_647_: *mut crate::leanh::LeanObject,
    mut v_a_648_: *mut crate::leanh::LeanObject,
    mut v_a_649_: *mut crate::leanh::LeanObject,
    mut v_a_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: u8 = 0;
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_663_: u8 = 0;
    let mut v_val_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: u8 = 0;
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_689_: u8 = 0;
    let mut v_val_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: u8 = 0;
    let mut v_value_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_694_: u8 = 0;
    let mut v_toSignature_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u8 = 0;
    let mut v_levelParams_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_709_: u8 = 0;
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_713_: u8 = 0;
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_718_: u8 = 0;
    let mut v_a_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_726_: u8 = 0;
    let mut v_a_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_734_: u8 = 0;
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: u8 = 0;
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v_val_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_746_: u8 = 0;
    let mut v_head_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: u8 = 0;
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_784_: u8 = 0;
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_788_: u8 = 0;
    let mut v_isSharedCheck_789_: u8 = 0;
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_792_: u8 = 0;
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_801_: u8 = 0;
    let mut v_a_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_658_ = 0;
                v___x_659_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                    v___x_658_,
                    v_fvarId_641_,
                    v_a_648_,
                );
                crate::leanh::lean_dec(v_fvarId_641_);
                if crate::leanh::lean_obj_tag(v___x_659_) == 0 {
                    v_a_660_ = crate::leanh::lean_ctor_get(v___x_659_, 0);
                    v_isSharedCheck_801_ = (!crate::leanh::lean_is_exclusive(v___x_659_)) as u8;
                    if v_isSharedCheck_801_ == 0 {
                        v___x_662_ = v___x_659_;
                        v_isShared_663_ = v_isSharedCheck_801_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_660_);
                        crate::leanh::lean_dec(v___x_659_);
                        v___x_662_ = crate::leanh::lean_box(0);
                        v_isShared_663_ = v_isSharedCheck_801_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_projs_642_);
                    v_a_802_ = crate::leanh::lean_ctor_get(v___x_659_, 0);
                    v_isSharedCheck_809_ = (!crate::leanh::lean_is_exclusive(v___x_659_)) as u8;
                    if v_isSharedCheck_809_ == 0 {
                        v___x_804_ = v___x_659_;
                        v_isShared_805_ = v_isSharedCheck_809_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_802_);
                        crate::leanh::lean_dec(v___x_659_);
                        v___x_804_ = crate::leanh::lean_box(0);
                        v_isShared_805_ = v_isSharedCheck_809_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_653_ = crate::leanh::lean_box(0);
                v___x_654_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_654_, 0, v___x_653_);
                return v___x_654_;
            }
            2 => {
                v___x_656_ = crate::leanh::lean_box(0);
                v___x_657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_657_, 0, v___x_656_);
                return v___x_657_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_660_) == 1 {
                    v_val_664_ = crate::leanh::lean_ctor_get(v_a_660_, 0);
                    crate::leanh::lean_inc(v_val_664_);
                    crate::leanh::lean_dec_ref_known(v_a_660_, 1);
                    v_value_665_ = crate::leanh::lean_ctor_get(v_val_664_, 3);
                    crate::leanh::lean_inc(v_value_665_);
                    crate::leanh::lean_dec(v_val_664_);
                    match crate::leanh::lean_obj_tag(v_value_665_) {
                        2 => {
                            crate::leanh::lean_del_object(v___x_662_);
                            v_idx_666_ = crate::leanh::lean_ctor_get(v_value_665_, 1);
                            crate::leanh::lean_inc(v_idx_666_);
                            v_struct_667_ = crate::leanh::lean_ctor_get(v_value_665_, 2);
                            crate::leanh::lean_inc(v_struct_667_);
                            crate::leanh::lean_dec_ref_known(v_value_665_, 3);
                            v___x_668_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_668_, 0, v_idx_666_);
                            crate::leanh::lean_ctor_set(v___x_668_, 1, v_projs_642_);
                            v_fvarId_641_ = v_struct_667_;
                            v_projs_642_ = v___x_668_;
                            state = 0;
                            continue;
                        }
                        3 => {
                            v_declName_670_ = crate::leanh::lean_ctor_get(v_value_665_, 0);
                            crate::leanh::lean_inc_n(v_declName_670_, 2);
                            v_us_671_ = crate::leanh::lean_ctor_get(v_value_665_, 1);
                            crate::leanh::lean_inc(v_us_671_);
                            v_args_672_ = crate::leanh::lean_ctor_get(v_value_665_, 2);
                            crate::leanh::lean_inc_ref(v_args_672_);
                            crate::leanh::lean_dec_ref_known(v_value_665_, 3);
                            v___x_735_ = lean_st_ref_get(v_a_650_);
                            v_env_736_ = crate::leanh::lean_ctor_get(v___x_735_, 0);
                            crate::leanh::lean_inc_ref(v_env_736_);
                            crate::leanh::lean_dec(v___x_735_);
                            v___x_737_ = 0;
                            v___x_738_ = l_Lean_Environment_find_x3f(
                                v_env_736_,
                                v_declName_670_,
                                v___x_737_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_738_) == 1 {
                                v_val_739_ = crate::leanh::lean_ctor_get(v___x_738_, 0);
                                v_isSharedCheck_792_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_738_)) as u8;
                                if v_isSharedCheck_792_ == 0 {
                                    v___x_741_ = v___x_738_;
                                    v_isShared_742_ = v_isSharedCheck_792_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_739_);
                                    crate::leanh::lean_dec(v___x_738_);
                                    v___x_741_ = crate::leanh::lean_box(0);
                                    v_isShared_742_ = v_isSharedCheck_792_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_738_);
                                crate::leanh::lean_del_object(v___x_662_);
                                v___y_674_ = v_a_643_;
                                v___y_675_ = v_a_644_;
                                v___y_676_ = v_a_645_;
                                v___y_677_ = v_a_646_;
                                v___y_678_ = v_a_647_;
                                v___y_679_ = v_a_648_;
                                v___y_680_ = v_a_649_;
                                v___y_681_ = v_a_650_;
                                state = 4;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_value_665_);
                            crate::leanh::lean_dec(v_projs_642_);
                            v___x_793_ = crate::leanh::lean_box(0);
                            if v_isShared_663_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_662_, 0, v___x_793_);
                                v___x_795_ = v___x_662_;
                                state = 21;
                                continue;
                            } else {
                                v_reuseFailAlloc_796_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
                                v___x_795_ = v_reuseFailAlloc_796_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_660_);
                    crate::leanh::lean_dec(v_projs_642_);
                    v___x_797_ = crate::leanh::lean_box(0);
                    if v_isShared_663_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_662_, 0, v___x_797_);
                        v___x_799_ = v___x_662_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
                        v___x_799_ = v_reuseFailAlloc_800_;
                        state = 22;
                        continue;
                    }
                }
            }
            4 => {
                v___x_682_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_678_);
                if crate::leanh::lean_obj_tag(v___x_682_) == 0 {
                    v_a_683_ = crate::leanh::lean_ctor_get(v___x_682_, 0);
                    crate::leanh::lean_inc(v_a_683_);
                    crate::leanh::lean_dec_ref_known(v___x_682_, 1);
                    v___x_684_ = (crate::leanh::lean_unbox(v_a_683_) as u8);
                    v___x_685_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                        v_declName_670_,
                        v___x_684_,
                        v___y_680_,
                        v___y_681_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_685_) == 0 {
                        v_a_686_ = crate::leanh::lean_ctor_get(v___x_685_, 0);
                        v_isSharedCheck_718_ = (!crate::leanh::lean_is_exclusive(v___x_685_)) as u8;
                        if v_isSharedCheck_718_ == 0 {
                            v___x_688_ = v___x_685_;
                            v_isShared_689_ = v_isSharedCheck_718_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_686_);
                            crate::leanh::lean_dec(v___x_685_);
                            v___x_688_ = crate::leanh::lean_box(0);
                            v_isShared_689_ = v_isSharedCheck_718_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_683_);
                        crate::leanh::lean_dec_ref(v_args_672_);
                        crate::leanh::lean_dec(v_us_671_);
                        crate::leanh::lean_dec(v_projs_642_);
                        v_a_719_ = crate::leanh::lean_ctor_get(v___x_685_, 0);
                        v_isSharedCheck_726_ = (!crate::leanh::lean_is_exclusive(v___x_685_)) as u8;
                        if v_isSharedCheck_726_ == 0 {
                            v___x_721_ = v___x_685_;
                            v_isShared_722_ = v_isSharedCheck_726_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_719_);
                            crate::leanh::lean_dec(v___x_685_);
                            v___x_721_ = crate::leanh::lean_box(0);
                            v_isShared_722_ = v_isSharedCheck_726_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_672_);
                    crate::leanh::lean_dec(v_us_671_);
                    crate::leanh::lean_dec(v_declName_670_);
                    crate::leanh::lean_dec(v_projs_642_);
                    v_a_727_ = crate::leanh::lean_ctor_get(v___x_682_, 0);
                    v_isSharedCheck_734_ = (!crate::leanh::lean_is_exclusive(v___x_682_)) as u8;
                    if v_isSharedCheck_734_ == 0 {
                        v___x_729_ = v___x_682_;
                        v_isShared_730_ = v_isSharedCheck_734_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_727_);
                        crate::leanh::lean_dec(v___x_682_);
                        v___x_729_ = crate::leanh::lean_box(0);
                        v_isShared_730_ = v_isSharedCheck_734_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_686_) == 1 {
                    v_val_690_ = crate::leanh::lean_ctor_get(v_a_686_, 0);
                    crate::leanh::lean_inc(v_val_690_);
                    crate::leanh::lean_dec_ref_known(v_a_686_, 1);
                    v___x_691_ = (crate::leanh::lean_unbox(v_a_683_) as u8);
                    crate::leanh::lean_dec(v_a_683_);
                    v___x_692_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_691_);
                    if v___x_692_ == 0 {
                        v_value_693_ = crate::leanh::lean_ctor_get(v_val_690_, 1);
                        if crate::leanh::lean_obj_tag(v_value_693_) == 0 {
                            crate::leanh::lean_del_object(v___x_688_);
                            v_recursive_694_ = crate::leanh::lean_ctor_get_uint8(
                                v_val_690_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            );
                            if v_recursive_694_ == 0 {
                                v_toSignature_695_ = crate::leanh::lean_ctor_get(v_val_690_, 0);
                                v_code_696_ = crate::leanh::lean_ctor_get(v_value_693_, 0);
                                crate::leanh::lean_inc_ref(v_code_696_);
                                v___x_697_ =
                                    l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_690_);
                                v___x_698_ = lean_array_get_size(v_args_672_);
                                v___x_699_ = lean_nat_dec_eq(v___x_697_, v___x_698_);
                                crate::leanh::lean_dec(v___x_697_);
                                if v___x_699_ == 0 {
                                    crate::leanh::lean_dec_ref(v_code_696_);
                                    crate::leanh::lean_dec(v_val_690_);
                                    crate::leanh::lean_dec_ref(v_args_672_);
                                    crate::leanh::lean_dec(v_us_671_);
                                    crate::leanh::lean_dec(v_projs_642_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_levelParams_700_ =
                                        crate::leanh::lean_ctor_get(v_toSignature_695_, 1);
                                    crate::leanh::lean_inc(v_levelParams_700_);
                                    crate::leanh::lean_inc(v_us_671_);
                                    v___x_701_ =
                                        l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(
                                            v___x_658_, v_val_690_, v_us_671_,
                                        );
                                    v___x_702_ =
                                        l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(
                                            v_code_696_,
                                            v_levelParams_700_,
                                            v_us_671_,
                                        );
                                    v___x_703_ = l_Lean_Compiler_LCNF_Simp_betaReduce(
                                        v___x_701_,
                                        v___x_702_,
                                        v_args_672_,
                                        v___x_699_,
                                        v___y_675_,
                                        v___y_676_,
                                        v___y_677_,
                                        v___y_678_,
                                        v___y_679_,
                                        v___y_680_,
                                        v___y_681_,
                                    );
                                    crate::leanh::lean_dec_ref(v___x_701_);
                                    if crate::leanh::lean_obj_tag(v___x_703_) == 0 {
                                        v_a_704_ = crate::leanh::lean_ctor_get(v___x_703_, 0);
                                        crate::leanh::lean_inc(v_a_704_);
                                        crate::leanh::lean_dec_ref_known(v___x_703_, 1);
                                        v___x_705_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_a_704_, v_projs_642_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
                                        return v___x_705_;
                                    } else {
                                        crate::leanh::lean_dec(v_projs_642_);
                                        v_a_706_ = crate::leanh::lean_ctor_get(v___x_703_, 0);
                                        v_isSharedCheck_713_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_703_)) as u8;
                                        if v_isSharedCheck_713_ == 0 {
                                            v___x_708_ = v___x_703_;
                                            v_isShared_709_ = v_isSharedCheck_713_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_706_);
                                            crate::leanh::lean_dec(v___x_703_);
                                            v___x_708_ = crate::leanh::lean_box(0);
                                            v_isShared_709_ = v_isSharedCheck_713_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_690_);
                                crate::leanh::lean_dec_ref(v_args_672_);
                                crate::leanh::lean_dec(v_us_671_);
                                crate::leanh::lean_dec(v_projs_642_);
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_690_);
                            crate::leanh::lean_dec_ref(v_args_672_);
                            crate::leanh::lean_dec(v_us_671_);
                            crate::leanh::lean_dec(v_projs_642_);
                            v___x_714_ = crate::leanh::lean_box(0);
                            if v_isShared_689_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_688_, 0, v___x_714_);
                                v___x_716_ = v___x_688_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_717_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
                                v___x_716_ = v_reuseFailAlloc_717_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_690_);
                        crate::leanh::lean_del_object(v___x_688_);
                        crate::leanh::lean_dec_ref(v_args_672_);
                        crate::leanh::lean_dec(v_us_671_);
                        crate::leanh::lean_dec(v_projs_642_);
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_688_);
                    crate::leanh::lean_dec(v_a_686_);
                    crate::leanh::lean_dec(v_a_683_);
                    crate::leanh::lean_dec_ref(v_args_672_);
                    crate::leanh::lean_dec(v_us_671_);
                    crate::leanh::lean_dec(v_projs_642_);
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_709_ == 0 {
                    v___x_711_ = v___x_708_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
                    v___x_711_ = v_reuseFailAlloc_712_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_711_;
            }
            8 => {
                return v___x_716_;
            }
            9 => {
                if v_isShared_722_ == 0 {
                    v___x_724_ = v___x_721_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
                    v___x_724_ = v_reuseFailAlloc_725_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_724_;
            }
            11 => {
                if v_isShared_730_ == 0 {
                    v___x_732_ = v___x_729_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
                    v___x_732_ = v_reuseFailAlloc_733_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_732_;
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_val_739_) == 6 {
                    crate::leanh::lean_dec(v_us_671_);
                    crate::leanh::lean_dec(v_declName_670_);
                    if crate::leanh::lean_obj_tag(v_projs_642_) == 1 {
                        v_val_743_ = crate::leanh::lean_ctor_get(v_val_739_, 0);
                        v_isSharedCheck_789_ = (!crate::leanh::lean_is_exclusive(v_val_739_)) as u8;
                        if v_isSharedCheck_789_ == 0 {
                            v___x_745_ = v_val_739_;
                            v_isShared_746_ = v_isSharedCheck_789_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_743_);
                            crate::leanh::lean_dec(v_val_739_);
                            v___x_745_ = crate::leanh::lean_box(0);
                            v_isShared_746_ = v_isSharedCheck_789_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_val_739_, 1);
                        crate::leanh::lean_del_object(v___x_741_);
                        crate::leanh::lean_dec_ref(v_args_672_);
                        crate::leanh::lean_del_object(v___x_662_);
                        crate::leanh::lean_dec(v_projs_642_);
                        v___x_790_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3_once), _init_l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3);
                        v___x_791_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v___x_790_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
                        return v___x_791_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_741_);
                    crate::leanh::lean_dec(v_val_739_);
                    crate::leanh::lean_del_object(v___x_662_);
                    v___y_674_ = v_a_643_;
                    v___y_675_ = v_a_644_;
                    v___y_676_ = v_a_645_;
                    v___y_677_ = v_a_646_;
                    v___y_678_ = v_a_647_;
                    v___y_679_ = v_a_648_;
                    v___y_680_ = v_a_649_;
                    v___y_681_ = v_a_650_;
                    state = 4;
                    continue;
                }
            }
            14 => {
                v_head_747_ = crate::leanh::lean_ctor_get(v_projs_642_, 0);
                crate::leanh::lean_inc(v_head_747_);
                v_tail_748_ = crate::leanh::lean_ctor_get(v_projs_642_, 1);
                crate::leanh::lean_inc(v_tail_748_);
                crate::leanh::lean_dec_ref_known(v_projs_642_, 2);
                v_numParams_767_ = crate::leanh::lean_ctor_get(v_val_743_, 3);
                crate::leanh::lean_inc(v_numParams_767_);
                crate::leanh::lean_dec_ref(v_val_743_);
                v___x_768_ = crate::leanh::lean_box(0);
                v___x_769_ = lean_nat_add(v_numParams_767_, v_head_747_);
                crate::leanh::lean_dec(v_head_747_);
                crate::leanh::lean_dec(v_numParams_767_);
                v___x_770_ = lean_array_get(v___x_768_, v_args_672_, v___x_769_);
                crate::leanh::lean_dec(v___x_769_);
                crate::leanh::lean_dec_ref(v_args_672_);
                if crate::leanh::lean_obj_tag(v___x_770_) == 1 {
                    crate::leanh::lean_del_object(v___x_745_);
                    v_fvarId_771_ = crate::leanh::lean_ctor_get(v___x_770_, 0);
                    crate::leanh::lean_inc(v_fvarId_771_);
                    crate::leanh::lean_dec_ref_known(v___x_770_, 1);
                    v_fvarId_750_ = v_fvarId_771_;
                    v___y_751_ = v_a_643_;
                    v___y_752_ = v_a_644_;
                    v___y_753_ = v_a_645_;
                    v___y_754_ = v_a_646_;
                    v___y_755_ = v_a_647_;
                    v___y_756_ = v_a_648_;
                    v___y_757_ = v_a_649_;
                    v___y_758_ = v_a_650_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_770_);
                    v___x_772_ = l_Lean_Compiler_LCNF_mkLetDeclErased(
                        v___x_658_, v_a_647_, v_a_648_, v_a_649_, v_a_650_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_772_) == 0 {
                        v_a_773_ = crate::leanh::lean_ctor_get(v___x_772_, 0);
                        crate::leanh::lean_inc_n(v_a_773_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_772_, 1);
                        v___x_774_ = lean_st_ref_take(v_a_643_);
                        if v_isShared_746_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_745_, 0);
                            crate::leanh::lean_ctor_set(v___x_745_, 0, v_a_773_);
                            v___x_776_ = v___x_745_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_780_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_773_);
                            v___x_776_ = v_reuseFailAlloc_780_;
                            state = 18;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_748_);
                        crate::leanh::lean_del_object(v___x_745_);
                        crate::leanh::lean_del_object(v___x_741_);
                        crate::leanh::lean_del_object(v___x_662_);
                        v_a_781_ = crate::leanh::lean_ctor_get(v___x_772_, 0);
                        v_isSharedCheck_788_ = (!crate::leanh::lean_is_exclusive(v___x_772_)) as u8;
                        if v_isSharedCheck_788_ == 0 {
                            v___x_783_ = v___x_772_;
                            v_isShared_784_ = v_isSharedCheck_788_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_781_);
                            crate::leanh::lean_dec(v___x_772_);
                            v___x_783_ = crate::leanh::lean_box(0);
                            v_isShared_784_ = v_isSharedCheck_788_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            15 => {
                v___x_759_ = l_List_isEmpty___redArg(v_tail_748_);
                if v___x_759_ == 0 {
                    crate::leanh::lean_del_object(v___x_741_);
                    crate::leanh::lean_del_object(v___x_662_);
                    v_fvarId_641_ = v_fvarId_750_;
                    v_projs_642_ = v_tail_748_;
                    v_a_643_ = v___y_751_;
                    v_a_644_ = v___y_752_;
                    v_a_645_ = v___y_753_;
                    v_a_646_ = v___y_754_;
                    v_a_647_ = v___y_755_;
                    v_a_648_ = v___y_756_;
                    v_a_649_ = v___y_757_;
                    v_a_650_ = v___y_758_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tail_748_);
                    if v_isShared_742_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_741_, 0, v_fvarId_750_);
                        v___x_762_ = v___x_741_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_766_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_766_, 0, v_fvarId_750_);
                        v___x_762_ = v_reuseFailAlloc_766_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_663_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_662_, 0, v___x_762_);
                    v___x_764_ = v___x_662_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
                    v___x_764_ = v_reuseFailAlloc_765_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_764_;
            }
            18 => {
                v___x_777_ = lean_array_push(v___x_774_, v___x_776_);
                v___x_778_ = lean_st_ref_set(v_a_643_, v___x_777_);
                v_fvarId_779_ = crate::leanh::lean_ctor_get(v_a_773_, 0);
                crate::leanh::lean_inc(v_fvarId_779_);
                crate::leanh::lean_dec(v_a_773_);
                v_fvarId_750_ = v_fvarId_779_;
                v___y_751_ = v_a_643_;
                v___y_752_ = v_a_644_;
                v___y_753_ = v_a_645_;
                v___y_754_ = v_a_646_;
                v___y_755_ = v_a_647_;
                v___y_756_ = v_a_648_;
                v___y_757_ = v_a_649_;
                v___y_758_ = v_a_650_;
                state = 15;
                continue;
            }
            19 => {
                if v_isShared_784_ == 0 {
                    v___x_786_ = v___x_783_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
                    v___x_786_ = v_reuseFailAlloc_787_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_786_;
            }
            21 => {
                return v___x_795_;
            }
            22 => {
                return v___x_799_;
            }
            23 => {
                if v_isShared_805_ == 0 {
                    v___x_807_ = v___x_804_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
                    v___x_807_ = v_reuseFailAlloc_808_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(
    mut v_code_810_: *mut crate::leanh::LeanObject,
    mut v_projs_811_: *mut crate::leanh::LeanObject,
    mut v_a_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
    mut v_a_814_: *mut crate::leanh::LeanObject,
    mut v_a_815_: *mut crate::leanh::LeanObject,
    mut v_a_816_: *mut crate::leanh::LeanObject,
    mut v_a_817_: *mut crate::leanh::LeanObject,
    mut v_a_818_: *mut crate::leanh::LeanObject,
    mut v_a_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: u8 = 0;
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_846_: u8 = 0;
    let mut v_unused_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_851_: u8 = 0;
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_810_) {
                0 => {
                    v_decl_821_ = crate::leanh::lean_ctor_get(v_code_810_, 0);
                    crate::leanh::lean_inc_ref(v_decl_821_);
                    v_k_822_ = crate::leanh::lean_ctor_get(v_code_810_, 1);
                    crate::leanh::lean_inc_ref(v_k_822_);
                    crate::leanh::lean_dec_ref_known(v_code_810_, 2);
                    v___x_823_ = lean_st_ref_take(v_a_812_);
                    v___x_824_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_824_, 0, v_decl_821_);
                    v___x_825_ = lean_array_push(v___x_823_, v___x_824_);
                    v___x_826_ = lean_st_ref_set(v_a_812_, v___x_825_);
                    v_code_810_ = v_k_822_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_828_ = crate::leanh::lean_ctor_get(v_code_810_, 0);
                    crate::leanh::lean_inc_ref(v_decl_828_);
                    v_k_829_ = crate::leanh::lean_ctor_get(v_code_810_, 1);
                    crate::leanh::lean_inc_ref(v_k_829_);
                    crate::leanh::lean_dec_ref_known(v_code_810_, 2);
                    v___x_830_ = lean_st_ref_take(v_a_812_);
                    v___x_831_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_831_, 0, v_decl_828_);
                    v___x_832_ = lean_array_push(v___x_830_, v___x_831_);
                    v___x_833_ = lean_st_ref_set(v_a_812_, v___x_832_);
                    v_code_810_ = v_k_829_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_fvarId_835_ = crate::leanh::lean_ctor_get(v_code_810_, 0);
                    crate::leanh::lean_inc(v_fvarId_835_);
                    crate::leanh::lean_dec_ref_known(v_code_810_, 1);
                    v___x_836_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_835_, v_projs_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
                    return v___x_836_;
                }
                _ => {
                    crate::leanh::lean_dec(v_projs_811_);
                    v___x_837_ = 0;
                    v___x_838_ =
                        l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_837_, v_code_810_, v_a_817_);
                    crate::leanh::lean_dec_ref(v_code_810_);
                    if crate::leanh::lean_obj_tag(v___x_838_) == 0 {
                        v_isSharedCheck_846_ = (!crate::leanh::lean_is_exclusive(v___x_838_)) as u8;
                        if v_isSharedCheck_846_ == 0 {
                            v_unused_847_ = crate::leanh::lean_ctor_get(v___x_838_, 0);
                            crate::leanh::lean_dec(v_unused_847_);
                            v___x_840_ = v___x_838_;
                            v_isShared_841_ = v_isSharedCheck_846_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_838_);
                            v___x_840_ = crate::leanh::lean_box(0);
                            v_isShared_841_ = v_isSharedCheck_846_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_848_ = crate::leanh::lean_ctor_get(v___x_838_, 0);
                        v_isSharedCheck_855_ = (!crate::leanh::lean_is_exclusive(v___x_838_)) as u8;
                        if v_isSharedCheck_855_ == 0 {
                            v___x_850_ = v___x_838_;
                            v_isShared_851_ = v_isSharedCheck_855_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_848_);
                            crate::leanh::lean_dec(v___x_838_);
                            v___x_850_ = crate::leanh::lean_box(0);
                            v_isShared_851_ = v_isSharedCheck_855_;
                            state = 3;
                            continue;
                        }
                    }
                }
            },
            1 => {
                v___x_842_ = crate::leanh::lean_box(0);
                if v_isShared_841_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_840_, 0, v___x_842_);
                    v___x_844_ = v___x_840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_845_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
                    v___x_844_ = v_reuseFailAlloc_845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_844_;
            }
            3 => {
                if v_isShared_851_ == 0 {
                    v___x_853_ = v___x_850_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_854_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
                    v___x_853_ = v_reuseFailAlloc_854_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode___boxed(
    mut v_code_856_: *mut crate::leanh::LeanObject,
    mut v_projs_857_: *mut crate::leanh::LeanObject,
    mut v_a_858_: *mut crate::leanh::LeanObject,
    mut v_a_859_: *mut crate::leanh::LeanObject,
    mut v_a_860_: *mut crate::leanh::LeanObject,
    mut v_a_861_: *mut crate::leanh::LeanObject,
    mut v_a_862_: *mut crate::leanh::LeanObject,
    mut v_a_863_: *mut crate::leanh::LeanObject,
    mut v_a_864_: *mut crate::leanh::LeanObject,
    mut v_a_865_: *mut crate::leanh::LeanObject,
    mut v_a_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_867_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_code_856_, v_projs_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
    crate::leanh::lean_dec(v_a_865_);
    crate::leanh::lean_dec_ref(v_a_864_);
    crate::leanh::lean_dec(v_a_863_);
    crate::leanh::lean_dec_ref(v_a_862_);
    crate::leanh::lean_dec_ref(v_a_861_);
    crate::leanh::lean_dec(v_a_860_);
    crate::leanh::lean_dec_ref(v_a_859_);
    crate::leanh::lean_dec(v_a_858_);
    return v_res_867_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___boxed(
    mut v_fvarId_868_: *mut crate::leanh::LeanObject,
    mut v_projs_869_: *mut crate::leanh::LeanObject,
    mut v_a_870_: *mut crate::leanh::LeanObject,
    mut v_a_871_: *mut crate::leanh::LeanObject,
    mut v_a_872_: *mut crate::leanh::LeanObject,
    mut v_a_873_: *mut crate::leanh::LeanObject,
    mut v_a_874_: *mut crate::leanh::LeanObject,
    mut v_a_875_: *mut crate::leanh::LeanObject,
    mut v_a_876_: *mut crate::leanh::LeanObject,
    mut v_a_877_: *mut crate::leanh::LeanObject,
    mut v_a_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_879_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_868_, v_projs_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
    crate::leanh::lean_dec(v_a_877_);
    crate::leanh::lean_dec_ref(v_a_876_);
    crate::leanh::lean_dec(v_a_875_);
    crate::leanh::lean_dec_ref(v_a_874_);
    crate::leanh::lean_dec_ref(v_a_873_);
    crate::leanh::lean_dec(v_a_872_);
    crate::leanh::lean_dec_ref(v_a_871_);
    crate::leanh::lean_dec(v_a_870_);
    return v_res_879_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(
    mut v_e_882_: *mut crate::leanh::LeanObject,
    mut v_a_883_: *mut crate::leanh::LeanObject,
    mut v_a_884_: *mut crate::leanh::LeanObject,
    mut v_a_885_: *mut crate::leanh::LeanObject,
    mut v_a_886_: *mut crate::leanh::LeanObject,
    mut v_a_887_: *mut crate::leanh::LeanObject,
    mut v_a_888_: *mut crate::leanh::LeanObject,
    mut v_a_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_idx_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: u8 = 0;
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_911_: u8 = 0;
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_920_: u8 = 0;
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_925_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut v_unused_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_947_: u8 = 0;
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut v_isSharedCheck_952_: u8 = 0;
    let mut v_a_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_956_: u8 = 0;
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_960_: u8 = 0;
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut v_a_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_973_: u8 = 0;
    let mut v_a_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_977_: u8 = 0;
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_981_: u8 = 0;
    let mut v_isSharedCheck_982_: u8 = 0;
    let mut v_a_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_986_: u8 = 0;
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_990_: u8 = 0;
    let mut v_a_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_882_) == 2 {
                    v_idx_891_ = crate::leanh::lean_ctor_get(v_e_882_, 1);
                    crate::leanh::lean_inc(v_idx_891_);
                    v_struct_892_ = crate::leanh::lean_ctor_get(v_e_882_, 2);
                    crate::leanh::lean_inc_n(v_struct_892_, 2);
                    v___x_893_ = l_Lean_Compiler_LCNF_getType(
                        v_struct_892_,
                        v_a_886_,
                        v_a_887_,
                        v_a_888_,
                        v_a_889_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_893_) == 0 {
                        v_a_894_ = crate::leanh::lean_ctor_get(v___x_893_, 0);
                        crate::leanh::lean_inc(v_a_894_);
                        crate::leanh::lean_dec_ref_known(v___x_893_, 1);
                        v___x_895_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_894_, v_a_889_);
                        crate::leanh::lean_dec(v_a_894_);
                        if crate::leanh::lean_obj_tag(v___x_895_) == 0 {
                            v_a_896_ = crate::leanh::lean_ctor_get(v___x_895_, 0);
                            v_isSharedCheck_982_ =
                                (!crate::leanh::lean_is_exclusive(v___x_895_)) as u8;
                            if v_isSharedCheck_982_ == 0 {
                                v___x_898_ = v___x_895_;
                                v_isShared_899_ = v_isSharedCheck_982_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_896_);
                                crate::leanh::lean_dec(v___x_895_);
                                v___x_898_ = crate::leanh::lean_box(0);
                                v_isShared_899_ = v_isSharedCheck_982_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_struct_892_);
                            crate::leanh::lean_dec(v_idx_891_);
                            crate::leanh::lean_dec_ref_known(v_e_882_, 3);
                            v_a_983_ = crate::leanh::lean_ctor_get(v___x_895_, 0);
                            v_isSharedCheck_990_ =
                                (!crate::leanh::lean_is_exclusive(v___x_895_)) as u8;
                            if v_isSharedCheck_990_ == 0 {
                                v___x_985_ = v___x_895_;
                                v_isShared_986_ = v_isSharedCheck_990_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_983_);
                                crate::leanh::lean_dec(v___x_895_);
                                v___x_985_ = crate::leanh::lean_box(0);
                                v_isShared_986_ = v_isSharedCheck_990_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_struct_892_);
                        crate::leanh::lean_dec(v_idx_891_);
                        crate::leanh::lean_dec_ref_known(v_e_882_, 3);
                        v_a_991_ = crate::leanh::lean_ctor_get(v___x_893_, 0);
                        v_isSharedCheck_998_ = (!crate::leanh::lean_is_exclusive(v___x_893_)) as u8;
                        if v_isSharedCheck_998_ == 0 {
                            v___x_993_ = v___x_893_;
                            v_isShared_994_ = v_isSharedCheck_998_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_991_);
                            crate::leanh::lean_dec(v___x_893_);
                            v___x_993_ = crate::leanh::lean_box(0);
                            v_isShared_994_ = v_isSharedCheck_998_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_e_882_);
                    v___x_999_ = crate::leanh::lean_box(0);
                    v___x_1000_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1000_, 0, v___x_999_);
                    return v___x_1000_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_896_) == 0 {
                    crate::leanh::lean_dec(v_struct_892_);
                    crate::leanh::lean_dec(v_idx_891_);
                    crate::leanh::lean_dec_ref_known(v_e_882_, 3);
                    v___x_900_ = crate::leanh::lean_box(0);
                    if v_isShared_899_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_898_, 0, v___x_900_);
                        v___x_902_ = v___x_898_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
                        v___x_902_ = v_reuseFailAlloc_903_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_896_, 1);
                    crate::leanh::lean_del_object(v___x_898_);
                    v___x_904_ = 0;
                    v___x_905_ = l_Lean_Compiler_LCNF_LetValue_inferType(
                        v___x_904_, v_e_882_, v_a_886_, v_a_887_, v_a_888_, v_a_889_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_905_) == 0 {
                        v_a_906_ = crate::leanh::lean_ctor_get(v___x_905_, 0);
                        crate::leanh::lean_inc(v_a_906_);
                        crate::leanh::lean_dec_ref_known(v___x_905_, 1);
                        v___x_907_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_906_, v_a_889_);
                        crate::leanh::lean_dec(v_a_906_);
                        if crate::leanh::lean_obj_tag(v___x_907_) == 0 {
                            v_a_908_ = crate::leanh::lean_ctor_get(v___x_907_, 0);
                            v_isSharedCheck_965_ =
                                (!crate::leanh::lean_is_exclusive(v___x_907_)) as u8;
                            if v_isSharedCheck_965_ == 0 {
                                v___x_910_ = v___x_907_;
                                v_isShared_911_ = v_isSharedCheck_965_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_908_);
                                crate::leanh::lean_dec(v___x_907_);
                                v___x_910_ = crate::leanh::lean_box(0);
                                v_isShared_911_ = v_isSharedCheck_965_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_struct_892_);
                            crate::leanh::lean_dec(v_idx_891_);
                            v_a_966_ = crate::leanh::lean_ctor_get(v___x_907_, 0);
                            v_isSharedCheck_973_ =
                                (!crate::leanh::lean_is_exclusive(v___x_907_)) as u8;
                            if v_isSharedCheck_973_ == 0 {
                                v___x_968_ = v___x_907_;
                                v_isShared_969_ = v_isSharedCheck_973_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_966_);
                                crate::leanh::lean_dec(v___x_907_);
                                v___x_968_ = crate::leanh::lean_box(0);
                                v_isShared_969_ = v_isSharedCheck_973_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_struct_892_);
                        crate::leanh::lean_dec(v_idx_891_);
                        v_a_974_ = crate::leanh::lean_ctor_get(v___x_905_, 0);
                        v_isSharedCheck_981_ = (!crate::leanh::lean_is_exclusive(v___x_905_)) as u8;
                        if v_isSharedCheck_981_ == 0 {
                            v___x_976_ = v___x_905_;
                            v_isShared_977_ = v_isSharedCheck_981_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_974_);
                            crate::leanh::lean_dec(v___x_905_);
                            v___x_976_ = crate::leanh::lean_box(0);
                            v_isShared_977_ = v_isSharedCheck_981_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_902_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_908_) == 0 {
                    crate::leanh::lean_del_object(v___x_910_);
                    v___x_912_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0;
                    v___x_913_ = lean_st_mk_ref(v___x_912_);
                    v___x_914_ = crate::leanh::lean_box(0);
                    v___x_915_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_915_, 0, v_idx_891_);
                    crate::leanh::lean_ctor_set(v___x_915_, 1, v___x_914_);
                    v___x_916_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_struct_892_, v___x_915_, v___x_913_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
                    if crate::leanh::lean_obj_tag(v___x_916_) == 0 {
                        v_a_917_ = crate::leanh::lean_ctor_get(v___x_916_, 0);
                        v_isSharedCheck_952_ = (!crate::leanh::lean_is_exclusive(v___x_916_)) as u8;
                        if v_isSharedCheck_952_ == 0 {
                            v___x_919_ = v___x_916_;
                            v_isShared_920_ = v_isSharedCheck_952_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_917_);
                            crate::leanh::lean_dec(v___x_916_);
                            v___x_919_ = crate::leanh::lean_box(0);
                            v_isShared_920_ = v_isSharedCheck_952_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_913_);
                        v_a_953_ = crate::leanh::lean_ctor_get(v___x_916_, 0);
                        v_isSharedCheck_960_ = (!crate::leanh::lean_is_exclusive(v___x_916_)) as u8;
                        if v_isSharedCheck_960_ == 0 {
                            v___x_955_ = v___x_916_;
                            v_isShared_956_ = v_isSharedCheck_960_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_953_);
                            crate::leanh::lean_dec(v___x_916_);
                            v___x_955_ = crate::leanh::lean_box(0);
                            v_isShared_956_ = v_isSharedCheck_960_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_908_, 1);
                    crate::leanh::lean_dec(v_struct_892_);
                    crate::leanh::lean_dec(v_idx_891_);
                    v___x_961_ = crate::leanh::lean_box(0);
                    if v_isShared_911_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_910_, 0, v___x_961_);
                        v___x_963_ = v___x_910_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_964_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
                        v___x_963_ = v_reuseFailAlloc_964_;
                        state = 14;
                        continue;
                    }
                }
            }
            4 => {
                v___x_921_ = lean_st_ref_get(v___x_913_);
                crate::leanh::lean_dec(v___x_913_);
                if crate::leanh::lean_obj_tag(v_a_917_) == 1 {
                    v_val_922_ = crate::leanh::lean_ctor_get(v_a_917_, 0);
                    v_isSharedCheck_933_ = (!crate::leanh::lean_is_exclusive(v_a_917_)) as u8;
                    if v_isSharedCheck_933_ == 0 {
                        v___x_924_ = v_a_917_;
                        v_isShared_925_ = v_isSharedCheck_933_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_922_);
                        crate::leanh::lean_dec(v_a_917_);
                        v___x_924_ = crate::leanh::lean_box(0);
                        v_isShared_925_ = v_isSharedCheck_933_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_919_);
                    crate::leanh::lean_dec(v_a_917_);
                    v___x_934_ = l_Lean_Compiler_LCNF_eraseCodeDecls(
                        v___x_904_, v___x_921_, v_a_886_, v_a_887_, v_a_888_, v_a_889_,
                    );
                    crate::leanh::lean_dec(v___x_921_);
                    if crate::leanh::lean_obj_tag(v___x_934_) == 0 {
                        v_isSharedCheck_942_ = (!crate::leanh::lean_is_exclusive(v___x_934_)) as u8;
                        if v_isSharedCheck_942_ == 0 {
                            v_unused_943_ = crate::leanh::lean_ctor_get(v___x_934_, 0);
                            crate::leanh::lean_dec(v_unused_943_);
                            v___x_936_ = v___x_934_;
                            v_isShared_937_ = v_isSharedCheck_942_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_934_);
                            v___x_936_ = crate::leanh::lean_box(0);
                            v_isShared_937_ = v_isSharedCheck_942_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_944_ = crate::leanh::lean_ctor_get(v___x_934_, 0);
                        v_isSharedCheck_951_ = (!crate::leanh::lean_is_exclusive(v___x_934_)) as u8;
                        if v_isSharedCheck_951_ == 0 {
                            v___x_946_ = v___x_934_;
                            v_isShared_947_ = v_isSharedCheck_951_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_944_);
                            crate::leanh::lean_dec(v___x_934_);
                            v___x_946_ = crate::leanh::lean_box(0);
                            v_isShared_947_ = v_isSharedCheck_951_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_926_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_926_, 0, v___x_921_);
                crate::leanh::lean_ctor_set(v___x_926_, 1, v_val_922_);
                if v_isShared_925_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_924_, 0, v___x_926_);
                    v___x_928_ = v___x_924_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_926_);
                    v___x_928_ = v_reuseFailAlloc_932_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_920_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_928_);
                    v___x_930_ = v___x_919_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
                    v___x_930_ = v_reuseFailAlloc_931_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_930_;
            }
            8 => {
                v___x_938_ = crate::leanh::lean_box(0);
                if v_isShared_937_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_938_);
                    v___x_940_ = v___x_936_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_941_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
                    v___x_940_ = v_reuseFailAlloc_941_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_940_;
            }
            10 => {
                if v_isShared_947_ == 0 {
                    v___x_949_ = v___x_946_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
                    v___x_949_ = v_reuseFailAlloc_950_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_949_;
            }
            12 => {
                if v_isShared_956_ == 0 {
                    v___x_958_ = v___x_955_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
                    v___x_958_ = v_reuseFailAlloc_959_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_958_;
            }
            14 => {
                return v___x_963_;
            }
            15 => {
                if v_isShared_969_ == 0 {
                    v___x_971_ = v___x_968_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
                    v___x_971_ = v_reuseFailAlloc_972_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_971_;
            }
            17 => {
                if v_isShared_977_ == 0 {
                    v___x_979_ = v___x_976_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_980_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
                    v___x_979_ = v_reuseFailAlloc_980_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_979_;
            }
            19 => {
                if v_isShared_986_ == 0 {
                    v___x_988_ = v___x_985_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
                    v___x_988_ = v_reuseFailAlloc_989_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_988_;
            }
            21 => {
                if v_isShared_994_ == 0 {
                    v___x_996_ = v___x_993_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___boxed(
    mut v_e_1001_: *mut crate::leanh::LeanObject,
    mut v_a_1002_: *mut crate::leanh::LeanObject,
    mut v_a_1003_: *mut crate::leanh::LeanObject,
    mut v_a_1004_: *mut crate::leanh::LeanObject,
    mut v_a_1005_: *mut crate::leanh::LeanObject,
    mut v_a_1006_: *mut crate::leanh::LeanObject,
    mut v_a_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
    mut v_a_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(
        v_e_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_,
    );
    crate::leanh::lean_dec(v_a_1008_);
    crate::leanh::lean_dec_ref(v_a_1007_);
    crate::leanh::lean_dec(v_a_1006_);
    crate::leanh::lean_dec_ref(v_a_1005_);
    crate::leanh::lean_dec_ref(v_a_1004_);
    crate::leanh::lean_dec(v_a_1003_);
    crate::leanh::lean_dec_ref(v_a_1002_);
    return v_res_1010_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_InlineProj(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_InlineProj(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
}
