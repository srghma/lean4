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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed as *const core::ffi::c_void, m_arity: 10, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1_value: LeanStringObject<92> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 73, 110, 108, 105, 110, 101, 80, 114, 111, 106, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 105, 110, 108, 105, 110, 101, 80, 114, 111, 106, 73, 110, 115, 116, 63, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 73, 110, 108, 105, 110, 101, 80, 114, 111, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0_value)
        as *mut LeanObject;
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    v___x_506_ = l_instMonadEIO(lean_box(0));
    return v___x_506_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(
    mut v_msg_513_: *mut LeanObject,
    mut v___y_514_: *mut LeanObject,
    mut v___y_515_: *mut LeanObject,
    mut v___y_516_: *mut LeanObject,
    mut v___y_517_: *mut LeanObject,
    mut v___y_518_: *mut LeanObject,
    mut v___y_519_: *mut LeanObject,
    mut v___y_520_: *mut LeanObject,
    mut v___y_521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_528_: u8 = 0;
    let mut v_toFunctor_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_535_: u8 = 0;
    let mut v___f_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_552_: u8 = 0;
    let mut v_toFunctor_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_559_: u8 = 0;
    let mut v___f_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_577_: u8 = 0;
    let mut v_toFunctor_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___f_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_24001__overap_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut v_unused_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_607_: u8 = 0;
    let mut v_unused_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v_unused_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_613_: u8 = 0;
    let mut v_unused_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut v_unused_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_unused_620_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_523_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0);
                v___x_524_ = l_StateRefT_x27_instMonad___redArg(v___x_523_);
                v_toApplicative_525_ = lean_ctor_get(v___x_524_, 0);
                v_isSharedCheck_619_ = (!lean_is_exclusive(v___x_524_)) as u8;
                if v_isSharedCheck_619_ == 0 {
                    v_unused_620_ = lean_ctor_get(v___x_524_, 1);
                    lean_dec(v_unused_620_);
                    v___x_527_ = v___x_524_;
                    v_isShared_528_ = v_isSharedCheck_619_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_525_);
                    lean_dec(v___x_524_);
                    v___x_527_ = lean_box(0);
                    v_isShared_528_ = v_isSharedCheck_619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_529_ = lean_ctor_get(v_toApplicative_525_, 0);
                v_toSeq_530_ = lean_ctor_get(v_toApplicative_525_, 2);
                v_toSeqLeft_531_ = lean_ctor_get(v_toApplicative_525_, 3);
                v_toSeqRight_532_ = lean_ctor_get(v_toApplicative_525_, 4);
                v_isSharedCheck_617_ = (!lean_is_exclusive(v_toApplicative_525_)) as u8;
                if v_isSharedCheck_617_ == 0 {
                    v_unused_618_ = lean_ctor_get(v_toApplicative_525_, 1);
                    lean_dec(v_unused_618_);
                    v___x_534_ = v_toApplicative_525_;
                    v_isShared_535_ = v_isSharedCheck_617_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_532_);
                    lean_inc(v_toSeqLeft_531_);
                    lean_inc(v_toSeq_530_);
                    lean_inc(v_toFunctor_529_);
                    lean_dec(v_toApplicative_525_);
                    v___x_534_ = lean_box(0);
                    v_isShared_535_ = v_isSharedCheck_617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_536_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1;
                v___f_537_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_529_);
                v___f_538_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_538_, 0, v_toFunctor_529_);
                v___f_539_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_539_, 0, v_toFunctor_529_);
                v___x_540_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_540_, 0, v___f_538_);
                lean_ctor_set(v___x_540_, 1, v___f_539_);
                v___f_541_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_541_, 0, v_toSeqRight_532_);
                v___f_542_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_542_, 0, v_toSeqLeft_531_);
                v___f_543_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_543_, 0, v_toSeq_530_);
                if v_isShared_535_ == 0 {
                    lean_ctor_set(v___x_534_, 4, v___f_541_);
                    lean_ctor_set(v___x_534_, 3, v___f_542_);
                    lean_ctor_set(v___x_534_, 2, v___f_543_);
                    lean_ctor_set(v___x_534_, 1, v___f_536_);
                    lean_ctor_set(v___x_534_, 0, v___x_540_);
                    v___x_545_ = v___x_534_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_540_);
                    lean_ctor_set(v_reuseFailAlloc_616_, 1, v___f_536_);
                    lean_ctor_set(v_reuseFailAlloc_616_, 2, v___f_543_);
                    lean_ctor_set(v_reuseFailAlloc_616_, 3, v___f_542_);
                    lean_ctor_set(v_reuseFailAlloc_616_, 4, v___f_541_);
                    v___x_545_ = v_reuseFailAlloc_616_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_528_ == 0 {
                    lean_ctor_set(v___x_527_, 1, v___f_537_);
                    lean_ctor_set(v___x_527_, 0, v___x_545_);
                    v___x_547_ = v___x_527_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_545_);
                    lean_ctor_set(v_reuseFailAlloc_615_, 1, v___f_537_);
                    v___x_547_ = v_reuseFailAlloc_615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_548_ = l_StateRefT_x27_instMonad___redArg(v___x_547_);
                v_toApplicative_549_ = lean_ctor_get(v___x_548_, 0);
                v_isSharedCheck_613_ = (!lean_is_exclusive(v___x_548_)) as u8;
                if v_isSharedCheck_613_ == 0 {
                    v_unused_614_ = lean_ctor_get(v___x_548_, 1);
                    lean_dec(v_unused_614_);
                    v___x_551_ = v___x_548_;
                    v_isShared_552_ = v_isSharedCheck_613_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_549_);
                    lean_dec(v___x_548_);
                    v___x_551_ = lean_box(0);
                    v_isShared_552_ = v_isSharedCheck_613_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_553_ = lean_ctor_get(v_toApplicative_549_, 0);
                v_toSeq_554_ = lean_ctor_get(v_toApplicative_549_, 2);
                v_toSeqLeft_555_ = lean_ctor_get(v_toApplicative_549_, 3);
                v_toSeqRight_556_ = lean_ctor_get(v_toApplicative_549_, 4);
                v_isSharedCheck_611_ = (!lean_is_exclusive(v_toApplicative_549_)) as u8;
                if v_isSharedCheck_611_ == 0 {
                    v_unused_612_ = lean_ctor_get(v_toApplicative_549_, 1);
                    lean_dec(v_unused_612_);
                    v___x_558_ = v_toApplicative_549_;
                    v_isShared_559_ = v_isSharedCheck_611_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_556_);
                    lean_inc(v_toSeqLeft_555_);
                    lean_inc(v_toSeq_554_);
                    lean_inc(v_toFunctor_553_);
                    lean_dec(v_toApplicative_549_);
                    v___x_558_ = lean_box(0);
                    v_isShared_559_ = v_isSharedCheck_611_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_560_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3;
                v___f_561_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4;
                lean_inc_ref(v_toFunctor_553_);
                v___f_562_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_562_, 0, v_toFunctor_553_);
                v___f_563_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_563_, 0, v_toFunctor_553_);
                v___x_564_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_564_, 0, v___f_562_);
                lean_ctor_set(v___x_564_, 1, v___f_563_);
                v___f_565_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_565_, 0, v_toSeqRight_556_);
                v___f_566_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_566_, 0, v_toSeqLeft_555_);
                v___f_567_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_567_, 0, v_toSeq_554_);
                if v_isShared_559_ == 0 {
                    lean_ctor_set(v___x_558_, 4, v___f_565_);
                    lean_ctor_set(v___x_558_, 3, v___f_566_);
                    lean_ctor_set(v___x_558_, 2, v___f_567_);
                    lean_ctor_set(v___x_558_, 1, v___f_560_);
                    lean_ctor_set(v___x_558_, 0, v___x_564_);
                    v___x_569_ = v___x_558_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_564_);
                    lean_ctor_set(v_reuseFailAlloc_610_, 1, v___f_560_);
                    lean_ctor_set(v_reuseFailAlloc_610_, 2, v___f_567_);
                    lean_ctor_set(v_reuseFailAlloc_610_, 3, v___f_566_);
                    lean_ctor_set(v_reuseFailAlloc_610_, 4, v___f_565_);
                    v___x_569_ = v_reuseFailAlloc_610_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_552_ == 0 {
                    lean_ctor_set(v___x_551_, 1, v___f_561_);
                    lean_ctor_set(v___x_551_, 0, v___x_569_);
                    v___x_571_ = v___x_551_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_569_);
                    lean_ctor_set(v_reuseFailAlloc_609_, 1, v___f_561_);
                    v___x_571_ = v_reuseFailAlloc_609_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_572_ = l_ReaderT_instMonad___redArg(v___x_571_);
                v___x_573_ = l_StateRefT_x27_instMonad___redArg(v___x_572_);
                v_toApplicative_574_ = lean_ctor_get(v___x_573_, 0);
                v_isSharedCheck_607_ = (!lean_is_exclusive(v___x_573_)) as u8;
                if v_isSharedCheck_607_ == 0 {
                    v_unused_608_ = lean_ctor_get(v___x_573_, 1);
                    lean_dec(v_unused_608_);
                    v___x_576_ = v___x_573_;
                    v_isShared_577_ = v_isSharedCheck_607_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_toApplicative_574_);
                    lean_dec(v___x_573_);
                    v___x_576_ = lean_box(0);
                    v_isShared_577_ = v_isSharedCheck_607_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_toFunctor_578_ = lean_ctor_get(v_toApplicative_574_, 0);
                v_toSeq_579_ = lean_ctor_get(v_toApplicative_574_, 2);
                v_toSeqLeft_580_ = lean_ctor_get(v_toApplicative_574_, 3);
                v_toSeqRight_581_ = lean_ctor_get(v_toApplicative_574_, 4);
                v_isSharedCheck_605_ = (!lean_is_exclusive(v_toApplicative_574_)) as u8;
                if v_isSharedCheck_605_ == 0 {
                    v_unused_606_ = lean_ctor_get(v_toApplicative_574_, 1);
                    lean_dec(v_unused_606_);
                    v___x_583_ = v_toApplicative_574_;
                    v_isShared_584_ = v_isSharedCheck_605_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_581_);
                    lean_inc(v_toSeqLeft_580_);
                    lean_inc(v_toSeq_579_);
                    lean_inc(v_toFunctor_578_);
                    lean_dec(v_toApplicative_574_);
                    v___x_583_ = lean_box(0);
                    v_isShared_584_ = v_isSharedCheck_605_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___f_585_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5;
                v___f_586_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6;
                lean_inc_ref(v_toFunctor_578_);
                v___f_587_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_587_, 0, v_toFunctor_578_);
                v___f_588_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_588_, 0, v_toFunctor_578_);
                v___x_589_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_589_, 0, v___f_587_);
                lean_ctor_set(v___x_589_, 1, v___f_588_);
                v___f_590_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_590_, 0, v_toSeqRight_581_);
                v___f_591_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_591_, 0, v_toSeqLeft_580_);
                v___f_592_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_592_, 0, v_toSeq_579_);
                if v_isShared_584_ == 0 {
                    lean_ctor_set(v___x_583_, 4, v___f_590_);
                    lean_ctor_set(v___x_583_, 3, v___f_591_);
                    lean_ctor_set(v___x_583_, 2, v___f_592_);
                    lean_ctor_set(v___x_583_, 1, v___f_585_);
                    lean_ctor_set(v___x_583_, 0, v___x_589_);
                    v___x_594_ = v___x_583_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_589_);
                    lean_ctor_set(v_reuseFailAlloc_604_, 1, v___f_585_);
                    lean_ctor_set(v_reuseFailAlloc_604_, 2, v___f_592_);
                    lean_ctor_set(v_reuseFailAlloc_604_, 3, v___f_591_);
                    lean_ctor_set(v_reuseFailAlloc_604_, 4, v___f_590_);
                    v___x_594_ = v_reuseFailAlloc_604_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_577_ == 0 {
                    lean_ctor_set(v___x_576_, 1, v___f_586_);
                    lean_ctor_set(v___x_576_, 0, v___x_594_);
                    v___x_596_ = v___x_576_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_594_);
                    lean_ctor_set(v_reuseFailAlloc_603_, 1, v___f_586_);
                    v___x_596_ = v_reuseFailAlloc_603_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_597_ = l_StateRefT_x27_instMonad___redArg(v___x_596_);
                v_toApplicative_598_ = lean_ctor_get(v___x_597_, 0);
                lean_inc_ref(v_toApplicative_598_);
                lean_dec_ref(v___x_597_);
                v_toPure_599_ = lean_ctor_get(v_toApplicative_598_, 1);
                lean_inc(v_toPure_599_);
                lean_dec_ref(v_toApplicative_598_);
                v___x_600_ = l_OptionT_instInhabitedOfPure___redArg(v_toPure_599_);
                v___x_24001__overap_601_ = lean_panic_fn_borrowed(v___x_600_, v_msg_513_);
                lean_dec(v___x_600_);
                lean_inc(v___y_521_);
                lean_inc_ref(v___y_520_);
                lean_inc(v___y_519_);
                lean_inc_ref(v___y_518_);
                lean_inc_ref(v___y_517_);
                lean_inc(v___y_516_);
                lean_inc_ref(v___y_515_);
                lean_inc(v___y_514_);
                v___x_602_ = lean_apply_9(
                    v___x_24001__overap_601_,
                    v___y_514_,
                    v___y_515_,
                    v___y_516_,
                    v___y_517_,
                    v___y_518_,
                    v___y_519_,
                    v___y_520_,
                    v___y_521_,
                    lean_box(0),
                );
                return v___x_602_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___boxed(
    mut v_msg_621_: *mut LeanObject,
    mut v___y_622_: *mut LeanObject,
    mut v___y_623_: *mut LeanObject,
    mut v___y_624_: *mut LeanObject,
    mut v___y_625_: *mut LeanObject,
    mut v___y_626_: *mut LeanObject,
    mut v___y_627_: *mut LeanObject,
    mut v___y_628_: *mut LeanObject,
    mut v___y_629_: *mut LeanObject,
    mut v___y_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_631_: *mut LeanObject = core::ptr::null_mut();
    v_res_631_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v_msg_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
    lean_dec(v___y_629_);
    lean_dec_ref(v___y_628_);
    lean_dec(v___y_627_);
    lean_dec_ref(v___y_626_);
    lean_dec_ref(v___y_625_);
    lean_dec(v___y_624_);
    lean_dec_ref(v___y_623_);
    lean_dec(v___y_622_);
    return v_res_631_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3()
-> *mut LeanObject {
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_635_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2;
    v___x_636_ = lean_unsigned_to_nat(34);
    v___x_637_ = lean_unsigned_to_nat(62);
    v___x_638_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1;
    v___x_639_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0;
    v___x_640_ =
        l_mkPanicMessageWithDecl(v___x_639_, v___x_638_, v___x_637_, v___x_636_, v___x_635_);
    return v___x_640_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(
    mut v_fvarId_641_: *mut LeanObject,
    mut v_projs_642_: *mut LeanObject,
    mut v_a_643_: *mut LeanObject,
    mut v_a_644_: *mut LeanObject,
    mut v_a_645_: *mut LeanObject,
    mut v_a_646_: *mut LeanObject,
    mut v_a_647_: *mut LeanObject,
    mut v_a_648_: *mut LeanObject,
    mut v_a_649_: *mut LeanObject,
    mut v_a_650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: u8 = 0;
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_663_: u8 = 0;
    let mut v_val_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: u8 = 0;
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_689_: u8 = 0;
    let mut v_val_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: u8 = 0;
    let mut v_value_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_694_: u8 = 0;
    let mut v_toSignature_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u8 = 0;
    let mut v_levelParams_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_709_: u8 = 0;
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_713_: u8 = 0;
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_718_: u8 = 0;
    let mut v_a_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_726_: u8 = 0;
    let mut v_a_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_734_: u8 = 0;
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: u8 = 0;
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v_val_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_746_: u8 = 0;
    let mut v_head_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: u8 = 0;
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_784_: u8 = 0;
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_788_: u8 = 0;
    let mut v_isSharedCheck_789_: u8 = 0;
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_792_: u8 = 0;
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_801_: u8 = 0;
    let mut v_a_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_808_: *mut LeanObject = core::ptr::null_mut();
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
                lean_dec(v_fvarId_641_);
                if lean_obj_tag(v___x_659_) == 0 {
                    v_a_660_ = lean_ctor_get(v___x_659_, 0);
                    v_isSharedCheck_801_ = (!lean_is_exclusive(v___x_659_)) as u8;
                    if v_isSharedCheck_801_ == 0 {
                        v___x_662_ = v___x_659_;
                        v_isShared_663_ = v_isSharedCheck_801_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_660_);
                        lean_dec(v___x_659_);
                        v___x_662_ = lean_box(0);
                        v_isShared_663_ = v_isSharedCheck_801_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_projs_642_);
                    v_a_802_ = lean_ctor_get(v___x_659_, 0);
                    v_isSharedCheck_809_ = (!lean_is_exclusive(v___x_659_)) as u8;
                    if v_isSharedCheck_809_ == 0 {
                        v___x_804_ = v___x_659_;
                        v_isShared_805_ = v_isSharedCheck_809_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_802_);
                        lean_dec(v___x_659_);
                        v___x_804_ = lean_box(0);
                        v_isShared_805_ = v_isSharedCheck_809_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_653_ = lean_box(0);
                v___x_654_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_654_, 0, v___x_653_);
                return v___x_654_;
            }
            2 => {
                v___x_656_ = lean_box(0);
                v___x_657_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_657_, 0, v___x_656_);
                return v___x_657_;
            }
            3 => {
                if lean_obj_tag(v_a_660_) == 1 {
                    v_val_664_ = lean_ctor_get(v_a_660_, 0);
                    lean_inc(v_val_664_);
                    lean_dec_ref_known(v_a_660_, 1);
                    v_value_665_ = lean_ctor_get(v_val_664_, 3);
                    lean_inc(v_value_665_);
                    lean_dec(v_val_664_);
                    match lean_obj_tag(v_value_665_) {
                        2 => {
                            lean_del_object(v___x_662_);
                            v_idx_666_ = lean_ctor_get(v_value_665_, 1);
                            lean_inc(v_idx_666_);
                            v_struct_667_ = lean_ctor_get(v_value_665_, 2);
                            lean_inc(v_struct_667_);
                            lean_dec_ref_known(v_value_665_, 3);
                            v___x_668_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_668_, 0, v_idx_666_);
                            lean_ctor_set(v___x_668_, 1, v_projs_642_);
                            v_fvarId_641_ = v_struct_667_;
                            v_projs_642_ = v___x_668_;
                            state = 0;
                            continue;
                        }
                        3 => {
                            v_declName_670_ = lean_ctor_get(v_value_665_, 0);
                            lean_inc_n(v_declName_670_, 2);
                            v_us_671_ = lean_ctor_get(v_value_665_, 1);
                            lean_inc(v_us_671_);
                            v_args_672_ = lean_ctor_get(v_value_665_, 2);
                            lean_inc_ref(v_args_672_);
                            lean_dec_ref_known(v_value_665_, 3);
                            v___x_735_ = lean_st_ref_get(v_a_650_);
                            v_env_736_ = lean_ctor_get(v___x_735_, 0);
                            lean_inc_ref(v_env_736_);
                            lean_dec(v___x_735_);
                            v___x_737_ = 0;
                            v___x_738_ = l_Lean_Environment_find_x3f(
                                v_env_736_,
                                v_declName_670_,
                                v___x_737_,
                            );
                            if lean_obj_tag(v___x_738_) == 1 {
                                v_val_739_ = lean_ctor_get(v___x_738_, 0);
                                v_isSharedCheck_792_ = (!lean_is_exclusive(v___x_738_)) as u8;
                                if v_isSharedCheck_792_ == 0 {
                                    v___x_741_ = v___x_738_;
                                    v_isShared_742_ = v_isSharedCheck_792_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_val_739_);
                                    lean_dec(v___x_738_);
                                    v___x_741_ = lean_box(0);
                                    v_isShared_742_ = v_isSharedCheck_792_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_738_);
                                lean_del_object(v___x_662_);
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
                            lean_dec(v_value_665_);
                            lean_dec(v_projs_642_);
                            v___x_793_ = lean_box(0);
                            if v_isShared_663_ == 0 {
                                lean_ctor_set(v___x_662_, 0, v___x_793_);
                                v___x_795_ = v___x_662_;
                                state = 21;
                                continue;
                            } else {
                                v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
                                v___x_795_ = v_reuseFailAlloc_796_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_660_);
                    lean_dec(v_projs_642_);
                    v___x_797_ = lean_box(0);
                    if v_isShared_663_ == 0 {
                        lean_ctor_set(v___x_662_, 0, v___x_797_);
                        v___x_799_ = v___x_662_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
                        v___x_799_ = v_reuseFailAlloc_800_;
                        state = 22;
                        continue;
                    }
                }
            }
            4 => {
                v___x_682_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_678_);
                if lean_obj_tag(v___x_682_) == 0 {
                    v_a_683_ = lean_ctor_get(v___x_682_, 0);
                    lean_inc(v_a_683_);
                    lean_dec_ref_known(v___x_682_, 1);
                    v___x_684_ = (lean_unbox(v_a_683_) as u8);
                    v___x_685_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                        v_declName_670_,
                        v___x_684_,
                        v___y_680_,
                        v___y_681_,
                    );
                    if lean_obj_tag(v___x_685_) == 0 {
                        v_a_686_ = lean_ctor_get(v___x_685_, 0);
                        v_isSharedCheck_718_ = (!lean_is_exclusive(v___x_685_)) as u8;
                        if v_isSharedCheck_718_ == 0 {
                            v___x_688_ = v___x_685_;
                            v_isShared_689_ = v_isSharedCheck_718_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_686_);
                            lean_dec(v___x_685_);
                            v___x_688_ = lean_box(0);
                            v_isShared_689_ = v_isSharedCheck_718_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_683_);
                        lean_dec_ref(v_args_672_);
                        lean_dec(v_us_671_);
                        lean_dec(v_projs_642_);
                        v_a_719_ = lean_ctor_get(v___x_685_, 0);
                        v_isSharedCheck_726_ = (!lean_is_exclusive(v___x_685_)) as u8;
                        if v_isSharedCheck_726_ == 0 {
                            v___x_721_ = v___x_685_;
                            v_isShared_722_ = v_isSharedCheck_726_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_719_);
                            lean_dec(v___x_685_);
                            v___x_721_ = lean_box(0);
                            v_isShared_722_ = v_isSharedCheck_726_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_args_672_);
                    lean_dec(v_us_671_);
                    lean_dec(v_declName_670_);
                    lean_dec(v_projs_642_);
                    v_a_727_ = lean_ctor_get(v___x_682_, 0);
                    v_isSharedCheck_734_ = (!lean_is_exclusive(v___x_682_)) as u8;
                    if v_isSharedCheck_734_ == 0 {
                        v___x_729_ = v___x_682_;
                        v_isShared_730_ = v_isSharedCheck_734_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_727_);
                        lean_dec(v___x_682_);
                        v___x_729_ = lean_box(0);
                        v_isShared_730_ = v_isSharedCheck_734_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_686_) == 1 {
                    v_val_690_ = lean_ctor_get(v_a_686_, 0);
                    lean_inc(v_val_690_);
                    lean_dec_ref_known(v_a_686_, 1);
                    v___x_691_ = (lean_unbox(v_a_683_) as u8);
                    lean_dec(v_a_683_);
                    v___x_692_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_691_);
                    if v___x_692_ == 0 {
                        v_value_693_ = lean_ctor_get(v_val_690_, 1);
                        if lean_obj_tag(v_value_693_) == 0 {
                            lean_del_object(v___x_688_);
                            v_recursive_694_ = lean_ctor_get_uint8(
                                v_val_690_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            if v_recursive_694_ == 0 {
                                v_toSignature_695_ = lean_ctor_get(v_val_690_, 0);
                                v_code_696_ = lean_ctor_get(v_value_693_, 0);
                                lean_inc_ref(v_code_696_);
                                v___x_697_ =
                                    l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_690_);
                                v___x_698_ = lean_array_get_size(v_args_672_);
                                v___x_699_ = lean_nat_dec_eq(v___x_697_, v___x_698_);
                                lean_dec(v___x_697_);
                                if v___x_699_ == 0 {
                                    lean_dec_ref(v_code_696_);
                                    lean_dec(v_val_690_);
                                    lean_dec_ref(v_args_672_);
                                    lean_dec(v_us_671_);
                                    lean_dec(v_projs_642_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_levelParams_700_ = lean_ctor_get(v_toSignature_695_, 1);
                                    lean_inc(v_levelParams_700_);
                                    lean_inc(v_us_671_);
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
                                    lean_dec_ref(v___x_701_);
                                    if lean_obj_tag(v___x_703_) == 0 {
                                        v_a_704_ = lean_ctor_get(v___x_703_, 0);
                                        lean_inc(v_a_704_);
                                        lean_dec_ref_known(v___x_703_, 1);
                                        v___x_705_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_a_704_, v_projs_642_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
                                        return v___x_705_;
                                    } else {
                                        lean_dec(v_projs_642_);
                                        v_a_706_ = lean_ctor_get(v___x_703_, 0);
                                        v_isSharedCheck_713_ =
                                            (!lean_is_exclusive(v___x_703_)) as u8;
                                        if v_isSharedCheck_713_ == 0 {
                                            v___x_708_ = v___x_703_;
                                            v_isShared_709_ = v_isSharedCheck_713_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_a_706_);
                                            lean_dec(v___x_703_);
                                            v___x_708_ = lean_box(0);
                                            v_isShared_709_ = v_isSharedCheck_713_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_val_690_);
                                lean_dec_ref(v_args_672_);
                                lean_dec(v_us_671_);
                                lean_dec(v_projs_642_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_690_);
                            lean_dec_ref(v_args_672_);
                            lean_dec(v_us_671_);
                            lean_dec(v_projs_642_);
                            v___x_714_ = lean_box(0);
                            if v_isShared_689_ == 0 {
                                lean_ctor_set(v___x_688_, 0, v___x_714_);
                                v___x_716_ = v___x_688_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
                                v___x_716_ = v_reuseFailAlloc_717_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_690_);
                        lean_del_object(v___x_688_);
                        lean_dec_ref(v_args_672_);
                        lean_dec(v_us_671_);
                        lean_dec(v_projs_642_);
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_688_);
                    lean_dec(v_a_686_);
                    lean_dec(v_a_683_);
                    lean_dec_ref(v_args_672_);
                    lean_dec(v_us_671_);
                    lean_dec(v_projs_642_);
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
                    v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
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
                    v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
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
                    v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
                    v___x_732_ = v_reuseFailAlloc_733_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_732_;
            }
            13 => {
                if lean_obj_tag(v_val_739_) == 6 {
                    lean_dec(v_us_671_);
                    lean_dec(v_declName_670_);
                    if lean_obj_tag(v_projs_642_) == 1 {
                        v_val_743_ = lean_ctor_get(v_val_739_, 0);
                        v_isSharedCheck_789_ = (!lean_is_exclusive(v_val_739_)) as u8;
                        if v_isSharedCheck_789_ == 0 {
                            v___x_745_ = v_val_739_;
                            v_isShared_746_ = v_isSharedCheck_789_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_val_743_);
                            lean_dec(v_val_739_);
                            v___x_745_ = lean_box(0);
                            v_isShared_746_ = v_isSharedCheck_789_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_val_739_, 1);
                        lean_del_object(v___x_741_);
                        lean_dec_ref(v_args_672_);
                        lean_del_object(v___x_662_);
                        lean_dec(v_projs_642_);
                        v___x_790_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3_once), _init_l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3);
                        v___x_791_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v___x_790_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
                        return v___x_791_;
                    }
                } else {
                    lean_del_object(v___x_741_);
                    lean_dec(v_val_739_);
                    lean_del_object(v___x_662_);
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
                v_head_747_ = lean_ctor_get(v_projs_642_, 0);
                lean_inc(v_head_747_);
                v_tail_748_ = lean_ctor_get(v_projs_642_, 1);
                lean_inc(v_tail_748_);
                lean_dec_ref_known(v_projs_642_, 2);
                v_numParams_767_ = lean_ctor_get(v_val_743_, 3);
                lean_inc(v_numParams_767_);
                lean_dec_ref(v_val_743_);
                v___x_768_ = lean_box(0);
                v___x_769_ = lean_nat_add(v_numParams_767_, v_head_747_);
                lean_dec(v_head_747_);
                lean_dec(v_numParams_767_);
                v___x_770_ = lean_array_get(v___x_768_, v_args_672_, v___x_769_);
                lean_dec(v___x_769_);
                lean_dec_ref(v_args_672_);
                if lean_obj_tag(v___x_770_) == 1 {
                    lean_del_object(v___x_745_);
                    v_fvarId_771_ = lean_ctor_get(v___x_770_, 0);
                    lean_inc(v_fvarId_771_);
                    lean_dec_ref_known(v___x_770_, 1);
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
                    lean_dec(v___x_770_);
                    v___x_772_ = l_Lean_Compiler_LCNF_mkLetDeclErased(
                        v___x_658_, v_a_647_, v_a_648_, v_a_649_, v_a_650_,
                    );
                    if lean_obj_tag(v___x_772_) == 0 {
                        v_a_773_ = lean_ctor_get(v___x_772_, 0);
                        lean_inc_n(v_a_773_, 2);
                        lean_dec_ref_known(v___x_772_, 1);
                        v___x_774_ = lean_st_ref_take(v_a_643_);
                        if v_isShared_746_ == 0 {
                            lean_ctor_set_tag(v___x_745_, 0);
                            lean_ctor_set(v___x_745_, 0, v_a_773_);
                            v___x_776_ = v___x_745_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_773_);
                            v___x_776_ = v_reuseFailAlloc_780_;
                            state = 18;
                            continue;
                        }
                    } else {
                        lean_dec(v_tail_748_);
                        lean_del_object(v___x_745_);
                        lean_del_object(v___x_741_);
                        lean_del_object(v___x_662_);
                        v_a_781_ = lean_ctor_get(v___x_772_, 0);
                        v_isSharedCheck_788_ = (!lean_is_exclusive(v___x_772_)) as u8;
                        if v_isSharedCheck_788_ == 0 {
                            v___x_783_ = v___x_772_;
                            v_isShared_784_ = v_isSharedCheck_788_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_781_);
                            lean_dec(v___x_772_);
                            v___x_783_ = lean_box(0);
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
                    lean_del_object(v___x_741_);
                    lean_del_object(v___x_662_);
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
                    lean_dec(v_tail_748_);
                    if v_isShared_742_ == 0 {
                        lean_ctor_set(v___x_741_, 0, v_fvarId_750_);
                        v___x_762_ = v___x_741_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_766_, 0, v_fvarId_750_);
                        v___x_762_ = v_reuseFailAlloc_766_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_663_ == 0 {
                    lean_ctor_set(v___x_662_, 0, v___x_762_);
                    v___x_764_ = v___x_662_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
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
                v_fvarId_779_ = lean_ctor_get(v_a_773_, 0);
                lean_inc(v_fvarId_779_);
                lean_dec(v_a_773_);
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
                    v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
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
                    v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
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
    mut v_code_810_: *mut LeanObject,
    mut v_projs_811_: *mut LeanObject,
    mut v_a_812_: *mut LeanObject,
    mut v_a_813_: *mut LeanObject,
    mut v_a_814_: *mut LeanObject,
    mut v_a_815_: *mut LeanObject,
    mut v_a_816_: *mut LeanObject,
    mut v_a_817_: *mut LeanObject,
    mut v_a_818_: *mut LeanObject,
    mut v_a_819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: u8 = 0;
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_846_: u8 = 0;
    let mut v_unused_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_851_: u8 = 0;
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_810_) {
                0 => {
                    v_decl_821_ = lean_ctor_get(v_code_810_, 0);
                    lean_inc_ref(v_decl_821_);
                    v_k_822_ = lean_ctor_get(v_code_810_, 1);
                    lean_inc_ref(v_k_822_);
                    lean_dec_ref_known(v_code_810_, 2);
                    v___x_823_ = lean_st_ref_take(v_a_812_);
                    v___x_824_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_824_, 0, v_decl_821_);
                    v___x_825_ = lean_array_push(v___x_823_, v___x_824_);
                    v___x_826_ = lean_st_ref_set(v_a_812_, v___x_825_);
                    v_code_810_ = v_k_822_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_828_ = lean_ctor_get(v_code_810_, 0);
                    lean_inc_ref(v_decl_828_);
                    v_k_829_ = lean_ctor_get(v_code_810_, 1);
                    lean_inc_ref(v_k_829_);
                    lean_dec_ref_known(v_code_810_, 2);
                    v___x_830_ = lean_st_ref_take(v_a_812_);
                    v___x_831_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_831_, 0, v_decl_828_);
                    v___x_832_ = lean_array_push(v___x_830_, v___x_831_);
                    v___x_833_ = lean_st_ref_set(v_a_812_, v___x_832_);
                    v_code_810_ = v_k_829_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_fvarId_835_ = lean_ctor_get(v_code_810_, 0);
                    lean_inc(v_fvarId_835_);
                    lean_dec_ref_known(v_code_810_, 1);
                    v___x_836_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_835_, v_projs_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
                    return v___x_836_;
                }
                _ => {
                    lean_dec(v_projs_811_);
                    v___x_837_ = 0;
                    v___x_838_ =
                        l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_837_, v_code_810_, v_a_817_);
                    lean_dec_ref(v_code_810_);
                    if lean_obj_tag(v___x_838_) == 0 {
                        v_isSharedCheck_846_ = (!lean_is_exclusive(v___x_838_)) as u8;
                        if v_isSharedCheck_846_ == 0 {
                            v_unused_847_ = lean_ctor_get(v___x_838_, 0);
                            lean_dec(v_unused_847_);
                            v___x_840_ = v___x_838_;
                            v_isShared_841_ = v_isSharedCheck_846_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_838_);
                            v___x_840_ = lean_box(0);
                            v_isShared_841_ = v_isSharedCheck_846_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_848_ = lean_ctor_get(v___x_838_, 0);
                        v_isSharedCheck_855_ = (!lean_is_exclusive(v___x_838_)) as u8;
                        if v_isSharedCheck_855_ == 0 {
                            v___x_850_ = v___x_838_;
                            v_isShared_851_ = v_isSharedCheck_855_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_848_);
                            lean_dec(v___x_838_);
                            v___x_850_ = lean_box(0);
                            v_isShared_851_ = v_isSharedCheck_855_;
                            state = 3;
                            continue;
                        }
                    }
                }
            },
            1 => {
                v___x_842_ = lean_box(0);
                if v_isShared_841_ == 0 {
                    lean_ctor_set(v___x_840_, 0, v___x_842_);
                    v___x_844_ = v___x_840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
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
                    v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
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
    mut v_code_856_: *mut LeanObject,
    mut v_projs_857_: *mut LeanObject,
    mut v_a_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
    mut v_a_860_: *mut LeanObject,
    mut v_a_861_: *mut LeanObject,
    mut v_a_862_: *mut LeanObject,
    mut v_a_863_: *mut LeanObject,
    mut v_a_864_: *mut LeanObject,
    mut v_a_865_: *mut LeanObject,
    mut v_a_866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_867_: *mut LeanObject = core::ptr::null_mut();
    v_res_867_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_code_856_, v_projs_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
    lean_dec(v_a_865_);
    lean_dec_ref(v_a_864_);
    lean_dec(v_a_863_);
    lean_dec_ref(v_a_862_);
    lean_dec_ref(v_a_861_);
    lean_dec(v_a_860_);
    lean_dec_ref(v_a_859_);
    lean_dec(v_a_858_);
    return v_res_867_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___boxed(
    mut v_fvarId_868_: *mut LeanObject,
    mut v_projs_869_: *mut LeanObject,
    mut v_a_870_: *mut LeanObject,
    mut v_a_871_: *mut LeanObject,
    mut v_a_872_: *mut LeanObject,
    mut v_a_873_: *mut LeanObject,
    mut v_a_874_: *mut LeanObject,
    mut v_a_875_: *mut LeanObject,
    mut v_a_876_: *mut LeanObject,
    mut v_a_877_: *mut LeanObject,
    mut v_a_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_879_: *mut LeanObject = core::ptr::null_mut();
    v_res_879_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_868_, v_projs_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
    lean_dec(v_a_877_);
    lean_dec_ref(v_a_876_);
    lean_dec(v_a_875_);
    lean_dec_ref(v_a_874_);
    lean_dec_ref(v_a_873_);
    lean_dec(v_a_872_);
    lean_dec_ref(v_a_871_);
    lean_dec(v_a_870_);
    return v_res_879_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(
    mut v_e_882_: *mut LeanObject,
    mut v_a_883_: *mut LeanObject,
    mut v_a_884_: *mut LeanObject,
    mut v_a_885_: *mut LeanObject,
    mut v_a_886_: *mut LeanObject,
    mut v_a_887_: *mut LeanObject,
    mut v_a_888_: *mut LeanObject,
    mut v_a_889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_idx_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: u8 = 0;
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_911_: u8 = 0;
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_920_: u8 = 0;
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_925_: u8 = 0;
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut v_unused_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_947_: u8 = 0;
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut v_isSharedCheck_952_: u8 = 0;
    let mut v_a_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_956_: u8 = 0;
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_960_: u8 = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut v_a_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_973_: u8 = 0;
    let mut v_a_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_977_: u8 = 0;
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_981_: u8 = 0;
    let mut v_isSharedCheck_982_: u8 = 0;
    let mut v_a_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_986_: u8 = 0;
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_990_: u8 = 0;
    let mut v_a_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_882_) == 2 {
                    v_idx_891_ = lean_ctor_get(v_e_882_, 1);
                    lean_inc(v_idx_891_);
                    v_struct_892_ = lean_ctor_get(v_e_882_, 2);
                    lean_inc_n(v_struct_892_, 2);
                    v___x_893_ = l_Lean_Compiler_LCNF_getType(
                        v_struct_892_,
                        v_a_886_,
                        v_a_887_,
                        v_a_888_,
                        v_a_889_,
                    );
                    if lean_obj_tag(v___x_893_) == 0 {
                        v_a_894_ = lean_ctor_get(v___x_893_, 0);
                        lean_inc(v_a_894_);
                        lean_dec_ref_known(v___x_893_, 1);
                        v___x_895_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_894_, v_a_889_);
                        lean_dec(v_a_894_);
                        if lean_obj_tag(v___x_895_) == 0 {
                            v_a_896_ = lean_ctor_get(v___x_895_, 0);
                            v_isSharedCheck_982_ = (!lean_is_exclusive(v___x_895_)) as u8;
                            if v_isSharedCheck_982_ == 0 {
                                v___x_898_ = v___x_895_;
                                v_isShared_899_ = v_isSharedCheck_982_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_896_);
                                lean_dec(v___x_895_);
                                v___x_898_ = lean_box(0);
                                v_isShared_899_ = v_isSharedCheck_982_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_struct_892_);
                            lean_dec(v_idx_891_);
                            lean_dec_ref_known(v_e_882_, 3);
                            v_a_983_ = lean_ctor_get(v___x_895_, 0);
                            v_isSharedCheck_990_ = (!lean_is_exclusive(v___x_895_)) as u8;
                            if v_isSharedCheck_990_ == 0 {
                                v___x_985_ = v___x_895_;
                                v_isShared_986_ = v_isSharedCheck_990_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_983_);
                                lean_dec(v___x_895_);
                                v___x_985_ = lean_box(0);
                                v_isShared_986_ = v_isSharedCheck_990_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_struct_892_);
                        lean_dec(v_idx_891_);
                        lean_dec_ref_known(v_e_882_, 3);
                        v_a_991_ = lean_ctor_get(v___x_893_, 0);
                        v_isSharedCheck_998_ = (!lean_is_exclusive(v___x_893_)) as u8;
                        if v_isSharedCheck_998_ == 0 {
                            v___x_993_ = v___x_893_;
                            v_isShared_994_ = v_isSharedCheck_998_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_991_);
                            lean_dec(v___x_893_);
                            v___x_993_ = lean_box(0);
                            v_isShared_994_ = v_isSharedCheck_998_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_e_882_);
                    v___x_999_ = lean_box(0);
                    v___x_1000_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1000_, 0, v___x_999_);
                    return v___x_1000_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_896_) == 0 {
                    lean_dec(v_struct_892_);
                    lean_dec(v_idx_891_);
                    lean_dec_ref_known(v_e_882_, 3);
                    v___x_900_ = lean_box(0);
                    if v_isShared_899_ == 0 {
                        lean_ctor_set(v___x_898_, 0, v___x_900_);
                        v___x_902_ = v___x_898_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
                        v___x_902_ = v_reuseFailAlloc_903_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_896_, 1);
                    lean_del_object(v___x_898_);
                    v___x_904_ = 0;
                    v___x_905_ = l_Lean_Compiler_LCNF_LetValue_inferType(
                        v___x_904_, v_e_882_, v_a_886_, v_a_887_, v_a_888_, v_a_889_,
                    );
                    if lean_obj_tag(v___x_905_) == 0 {
                        v_a_906_ = lean_ctor_get(v___x_905_, 0);
                        lean_inc(v_a_906_);
                        lean_dec_ref_known(v___x_905_, 1);
                        v___x_907_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_906_, v_a_889_);
                        lean_dec(v_a_906_);
                        if lean_obj_tag(v___x_907_) == 0 {
                            v_a_908_ = lean_ctor_get(v___x_907_, 0);
                            v_isSharedCheck_965_ = (!lean_is_exclusive(v___x_907_)) as u8;
                            if v_isSharedCheck_965_ == 0 {
                                v___x_910_ = v___x_907_;
                                v_isShared_911_ = v_isSharedCheck_965_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_908_);
                                lean_dec(v___x_907_);
                                v___x_910_ = lean_box(0);
                                v_isShared_911_ = v_isSharedCheck_965_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_struct_892_);
                            lean_dec(v_idx_891_);
                            v_a_966_ = lean_ctor_get(v___x_907_, 0);
                            v_isSharedCheck_973_ = (!lean_is_exclusive(v___x_907_)) as u8;
                            if v_isSharedCheck_973_ == 0 {
                                v___x_968_ = v___x_907_;
                                v_isShared_969_ = v_isSharedCheck_973_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_966_);
                                lean_dec(v___x_907_);
                                v___x_968_ = lean_box(0);
                                v_isShared_969_ = v_isSharedCheck_973_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_struct_892_);
                        lean_dec(v_idx_891_);
                        v_a_974_ = lean_ctor_get(v___x_905_, 0);
                        v_isSharedCheck_981_ = (!lean_is_exclusive(v___x_905_)) as u8;
                        if v_isSharedCheck_981_ == 0 {
                            v___x_976_ = v___x_905_;
                            v_isShared_977_ = v_isSharedCheck_981_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_974_);
                            lean_dec(v___x_905_);
                            v___x_976_ = lean_box(0);
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
                if lean_obj_tag(v_a_908_) == 0 {
                    lean_del_object(v___x_910_);
                    v___x_912_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0;
                    v___x_913_ = lean_st_mk_ref(v___x_912_);
                    v___x_914_ = lean_box(0);
                    v___x_915_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_915_, 0, v_idx_891_);
                    lean_ctor_set(v___x_915_, 1, v___x_914_);
                    v___x_916_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_struct_892_, v___x_915_, v___x_913_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
                    if lean_obj_tag(v___x_916_) == 0 {
                        v_a_917_ = lean_ctor_get(v___x_916_, 0);
                        v_isSharedCheck_952_ = (!lean_is_exclusive(v___x_916_)) as u8;
                        if v_isSharedCheck_952_ == 0 {
                            v___x_919_ = v___x_916_;
                            v_isShared_920_ = v_isSharedCheck_952_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_917_);
                            lean_dec(v___x_916_);
                            v___x_919_ = lean_box(0);
                            v_isShared_920_ = v_isSharedCheck_952_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_913_);
                        v_a_953_ = lean_ctor_get(v___x_916_, 0);
                        v_isSharedCheck_960_ = (!lean_is_exclusive(v___x_916_)) as u8;
                        if v_isSharedCheck_960_ == 0 {
                            v___x_955_ = v___x_916_;
                            v_isShared_956_ = v_isSharedCheck_960_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_953_);
                            lean_dec(v___x_916_);
                            v___x_955_ = lean_box(0);
                            v_isShared_956_ = v_isSharedCheck_960_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_908_, 1);
                    lean_dec(v_struct_892_);
                    lean_dec(v_idx_891_);
                    v___x_961_ = lean_box(0);
                    if v_isShared_911_ == 0 {
                        lean_ctor_set(v___x_910_, 0, v___x_961_);
                        v___x_963_ = v___x_910_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
                        v___x_963_ = v_reuseFailAlloc_964_;
                        state = 14;
                        continue;
                    }
                }
            }
            4 => {
                v___x_921_ = lean_st_ref_get(v___x_913_);
                lean_dec(v___x_913_);
                if lean_obj_tag(v_a_917_) == 1 {
                    v_val_922_ = lean_ctor_get(v_a_917_, 0);
                    v_isSharedCheck_933_ = (!lean_is_exclusive(v_a_917_)) as u8;
                    if v_isSharedCheck_933_ == 0 {
                        v___x_924_ = v_a_917_;
                        v_isShared_925_ = v_isSharedCheck_933_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_922_);
                        lean_dec(v_a_917_);
                        v___x_924_ = lean_box(0);
                        v_isShared_925_ = v_isSharedCheck_933_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_919_);
                    lean_dec(v_a_917_);
                    v___x_934_ = l_Lean_Compiler_LCNF_eraseCodeDecls(
                        v___x_904_, v___x_921_, v_a_886_, v_a_887_, v_a_888_, v_a_889_,
                    );
                    lean_dec(v___x_921_);
                    if lean_obj_tag(v___x_934_) == 0 {
                        v_isSharedCheck_942_ = (!lean_is_exclusive(v___x_934_)) as u8;
                        if v_isSharedCheck_942_ == 0 {
                            v_unused_943_ = lean_ctor_get(v___x_934_, 0);
                            lean_dec(v_unused_943_);
                            v___x_936_ = v___x_934_;
                            v_isShared_937_ = v_isSharedCheck_942_;
                            state = 8;
                            continue;
                        } else {
                            lean_dec(v___x_934_);
                            v___x_936_ = lean_box(0);
                            v_isShared_937_ = v_isSharedCheck_942_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_944_ = lean_ctor_get(v___x_934_, 0);
                        v_isSharedCheck_951_ = (!lean_is_exclusive(v___x_934_)) as u8;
                        if v_isSharedCheck_951_ == 0 {
                            v___x_946_ = v___x_934_;
                            v_isShared_947_ = v_isSharedCheck_951_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_944_);
                            lean_dec(v___x_934_);
                            v___x_946_ = lean_box(0);
                            v_isShared_947_ = v_isSharedCheck_951_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_926_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_926_, 0, v___x_921_);
                lean_ctor_set(v___x_926_, 1, v_val_922_);
                if v_isShared_925_ == 0 {
                    lean_ctor_set(v___x_924_, 0, v___x_926_);
                    v___x_928_ = v___x_924_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_926_);
                    v___x_928_ = v_reuseFailAlloc_932_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_920_ == 0 {
                    lean_ctor_set(v___x_919_, 0, v___x_928_);
                    v___x_930_ = v___x_919_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
                    v___x_930_ = v_reuseFailAlloc_931_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_930_;
            }
            8 => {
                v___x_938_ = lean_box(0);
                if v_isShared_937_ == 0 {
                    lean_ctor_set(v___x_936_, 0, v___x_938_);
                    v___x_940_ = v___x_936_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
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
                    v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
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
                    v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
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
                    v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
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
                    v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
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
                    v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
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
                    v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
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
    mut v_e_1001_: *mut LeanObject,
    mut v_a_1002_: *mut LeanObject,
    mut v_a_1003_: *mut LeanObject,
    mut v_a_1004_: *mut LeanObject,
    mut v_a_1005_: *mut LeanObject,
    mut v_a_1006_: *mut LeanObject,
    mut v_a_1007_: *mut LeanObject,
    mut v_a_1008_: *mut LeanObject,
    mut v_a_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1010_: *mut LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(
        v_e_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_,
    );
    lean_dec(v_a_1008_);
    lean_dec_ref(v_a_1007_);
    lean_dec(v_a_1006_);
    lean_dec_ref(v_a_1005_);
    lean_dec_ref(v_a_1004_);
    lean_dec(v_a_1003_);
    lean_dec_ref(v_a_1002_);
    return v_res_1010_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
}
