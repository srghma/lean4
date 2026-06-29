// Lean compiler output
// Module: Lean.Compiler.LCNF.EmitUtil
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PhaseExt Lean.Compiler.InitAttr
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt, lean_panic_fn_borrowed,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append,
    lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
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
use crate::r#gen::Lean::Compiler::InitAttr::{
    initialize_Lean_Compiler_InitAttr, l_Lean_getBuiltinInitFnNameFor_x3f,
    lean_get_init_fn_name_for, runtime_initialize_Lean_Compiler_InitAttr,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg,
    l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_header;
use crate::r#gen::Lean::Setup::l_Lean_instBEqIRPhases_beq;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 109, 105, 116, 85, 116, 105, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1_value: crate::leanh::LeanStringObject<78> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 109, 105, 116, 85, 116, 105, 108, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 99, 111, 108, 108, 101, 99, 116, 85, 115, 101, 100, 68, 101, 99, 108, 115, 46, 103, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2_value: crate::leanh::LeanStringObject<64> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [99, 111, 108, 108, 101, 99, 116, 85, 115, 101, 100, 68, 101, 99, 108, 115, 58, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 111, 114, 32, 115, 105, 103, 110, 97, 116, 117, 114, 101, 32, 102, 111, 114, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_collectUsedDecls___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Compiler_LCNF_collectUsedDecls___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_collectUsedDecls___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_collectUsedDecls___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_collectUsedDecls___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_479_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_479_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(
    mut v_msg_482_: *mut crate::leanh::LeanObject,
    mut v___y_483_: *mut crate::leanh::LeanObject,
    mut v___y_484_: *mut crate::leanh::LeanObject,
    mut v___y_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v_toFunctor_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_499_: u8 = 0;
    let mut v___f_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823__overap_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut v_unused_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_521_: u8 = 0;
    let mut v_unused_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_487_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0);
                v___x_488_ = l_StateRefT_x27_instMonad___redArg(v___x_487_);
                v_toApplicative_489_ = crate::leanh::lean_ctor_get(v___x_488_, 0);
                v_isSharedCheck_521_ = (!crate::leanh::lean_is_exclusive(v___x_488_)) as u8;
                if v_isSharedCheck_521_ == 0 {
                    v_unused_522_ = crate::leanh::lean_ctor_get(v___x_488_, 1);
                    crate::leanh::lean_dec(v_unused_522_);
                    v___x_491_ = v___x_488_;
                    v_isShared_492_ = v_isSharedCheck_521_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_489_);
                    crate::leanh::lean_dec(v___x_488_);
                    v___x_491_ = crate::leanh::lean_box(0);
                    v_isShared_492_ = v_isSharedCheck_521_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_493_ = crate::leanh::lean_ctor_get(v_toApplicative_489_, 0);
                v_toSeq_494_ = crate::leanh::lean_ctor_get(v_toApplicative_489_, 2);
                v_toSeqLeft_495_ = crate::leanh::lean_ctor_get(v_toApplicative_489_, 3);
                v_toSeqRight_496_ = crate::leanh::lean_ctor_get(v_toApplicative_489_, 4);
                v_isSharedCheck_519_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_489_)) as u8;
                if v_isSharedCheck_519_ == 0 {
                    v_unused_520_ = crate::leanh::lean_ctor_get(v_toApplicative_489_, 1);
                    crate::leanh::lean_dec(v_unused_520_);
                    v___x_498_ = v_toApplicative_489_;
                    v_isShared_499_ = v_isSharedCheck_519_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_496_);
                    crate::leanh::lean_inc(v_toSeqLeft_495_);
                    crate::leanh::lean_inc(v_toSeq_494_);
                    crate::leanh::lean_inc(v_toFunctor_493_);
                    crate::leanh::lean_dec(v_toApplicative_489_);
                    v___x_498_ = crate::leanh::lean_box(0);
                    v_isShared_499_ = v_isSharedCheck_519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_500_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1;
                v___f_501_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_493_);
                v___f_502_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_502_, 0, v_toFunctor_493_);
                v___f_503_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_503_, 0, v_toFunctor_493_);
                v___x_504_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_504_, 0, v___f_502_);
                crate::leanh::lean_ctor_set(v___x_504_, 1, v___f_503_);
                v___f_505_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_505_, 0, v_toSeqRight_496_);
                v___f_506_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_506_, 0, v_toSeqLeft_495_);
                v___f_507_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_507_, 0, v_toSeq_494_);
                if v_isShared_499_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_498_, 4, v___f_505_);
                    crate::leanh::lean_ctor_set(v___x_498_, 3, v___f_506_);
                    crate::leanh::lean_ctor_set(v___x_498_, 2, v___f_507_);
                    crate::leanh::lean_ctor_set(v___x_498_, 1, v___f_500_);
                    crate::leanh::lean_ctor_set(v___x_498_, 0, v___x_504_);
                    v___x_509_ = v___x_498_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_518_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 1, v___f_500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 2, v___f_507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 3, v___f_506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 4, v___f_505_);
                    v___x_509_ = v_reuseFailAlloc_518_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_492_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_491_, 1, v___f_501_);
                    crate::leanh::lean_ctor_set(v___x_491_, 0, v___x_509_);
                    v___x_511_ = v___x_491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_517_, 1, v___f_501_);
                    v___x_511_ = v_reuseFailAlloc_517_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_512_ = l_StateRefT_x27_instMonad___redArg(v___x_511_);
                v___x_513_ = crate::leanh::lean_box(0);
                v___x_514_ = l_instInhabitedOfMonad___redArg(v___x_512_, v___x_513_);
                v___x_5823__overap_515_ = lean_panic_fn_borrowed(v___x_514_, v_msg_482_);
                crate::leanh::lean_dec(v___x_514_);
                crate::leanh::lean_inc(v___y_485_);
                crate::leanh::lean_inc_ref(v___y_484_);
                crate::leanh::lean_inc(v___y_483_);
                v___x_516_ = crate::leanh::lean_apply_4(
                    v___x_5823__overap_515_,
                    v___y_483_,
                    v___y_484_,
                    v___y_485_,
                    crate::leanh::lean_box(0),
                );
                return v___x_516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___boxed(
    mut v_msg_523_: *mut crate::leanh::LeanObject,
    mut v___y_524_: *mut crate::leanh::LeanObject,
    mut v___y_525_: *mut crate::leanh::LeanObject,
    mut v___y_526_: *mut crate::leanh::LeanObject,
    mut v___y_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_528_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v_msg_523_, v___y_524_, v___y_525_, v___y_526_);
    crate::leanh::lean_dec(v___y_526_);
    crate::leanh::lean_dec_ref(v___y_525_);
    crate::leanh::lean_dec(v___y_524_);
    return v_res_528_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(
    mut v_f_529_: *mut crate::leanh::LeanObject,
    mut v_v_530_: *mut crate::leanh::LeanObject,
    mut v___y_531_: *mut crate::leanh::LeanObject,
    mut v___y_532_: *mut crate::leanh::LeanObject,
    mut v___y_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_539_: u8 = 0;
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_544_: u8 = 0;
    let mut v_unused_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_530_) == 0 {
                    v_code_535_ = crate::leanh::lean_ctor_get(v_v_530_, 0);
                    crate::leanh::lean_inc_ref(v_code_535_);
                    crate::leanh::lean_dec_ref_known(v_v_530_, 1);
                    crate::leanh::lean_inc(v___y_533_);
                    crate::leanh::lean_inc_ref(v___y_532_);
                    crate::leanh::lean_inc(v___y_531_);
                    v___x_536_ = crate::leanh::lean_apply_5(
                        v_f_529_,
                        v_code_535_,
                        v___y_531_,
                        v___y_532_,
                        v___y_533_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_536_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_529_);
                    v_isSharedCheck_544_ = (!crate::leanh::lean_is_exclusive(v_v_530_)) as u8;
                    if v_isSharedCheck_544_ == 0 {
                        v_unused_545_ = crate::leanh::lean_ctor_get(v_v_530_, 0);
                        crate::leanh::lean_dec(v_unused_545_);
                        v___x_538_ = v_v_530_;
                        v_isShared_539_ = v_isSharedCheck_544_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_530_);
                        v___x_538_ = crate::leanh::lean_box(0);
                        v_isShared_539_ = v_isSharedCheck_544_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_540_ = crate::leanh::lean_box(0);
                if v_isShared_539_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_538_, 0);
                    crate::leanh::lean_ctor_set(v___x_538_, 0, v___x_540_);
                    v___x_542_ = v___x_538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
                    v___x_542_ = v_reuseFailAlloc_543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg___boxed(
    mut v_f_546_: *mut crate::leanh::LeanObject,
    mut v_v_547_: *mut crate::leanh::LeanObject,
    mut v___y_548_: *mut crate::leanh::LeanObject,
    mut v___y_549_: *mut crate::leanh::LeanObject,
    mut v___y_550_: *mut crate::leanh::LeanObject,
    mut v___y_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_552_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_546_, v_v_547_, v___y_548_, v___y_549_, v___y_550_);
    crate::leanh::lean_dec(v___y_550_);
    crate::leanh::lean_dec_ref(v___y_549_);
    crate::leanh::lean_dec(v___y_548_);
    return v_res_552_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0___boxed(
    mut v___x_553_: *mut crate::leanh::LeanObject,
    mut v_x_554_: *mut crate::leanh::LeanObject,
    mut v___y_555_: *mut crate::leanh::LeanObject,
    mut v___y_556_: *mut crate::leanh::LeanObject,
    mut v___y_557_: *mut crate::leanh::LeanObject,
    mut v___y_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6627__boxed_559_: u8 = 0;
    let mut v_res_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6627__boxed_559_ = (crate::leanh::lean_unbox(v___x_553_) as u8);
    v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(v___x_6627__boxed_559_, v_x_554_, v___y_555_, v___y_556_, v___y_557_);
    crate::leanh::lean_dec(v___y_557_);
    crate::leanh::lean_dec_ref(v___y_556_);
    crate::leanh::lean_dec(v___y_555_);
    return v_res_560_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(
    mut v_as_565_: *mut crate::leanh::LeanObject,
    mut v_i_566_: usize,
    mut v_stop_567_: usize,
    mut v_b_568_: *mut crate::leanh::LeanObject,
    mut v___y_569_: *mut crate::leanh::LeanObject,
    mut v___y_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: usize = 0;
    let mut v___x_576_: usize = 0;
    let mut v___y_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localDecls_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extSigs_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_592_: u8 = 0;
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localDecls_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extSigs_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_606_: u8 = 0;
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: u8 = 0;
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localDecls_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extSigs_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_648_: u8 = 0;
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_664_: u8 = 0;
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut v_a_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_672_: u8 = 0;
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_676_: u8 = 0;
    let mut v_reuseFailAlloc_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_678_: u8 = 0;
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_581_ = lean_usize_dec_eq(v_i_566_, v_stop_567_);
                if v___x_581_ == 0 {
                    v___x_582_ = lean_st_ref_get(v___y_569_);
                    v_visited_583_ = crate::leanh::lean_ctor_get(v___x_582_, 0);
                    crate::leanh::lean_inc(v_visited_583_);
                    crate::leanh::lean_dec(v___x_582_);
                    v___x_584_ = lean_array_uget_borrowed(v_as_565_, v_i_566_);
                    v___x_585_ = l_Lean_NameSet_contains(v_visited_583_, v___x_584_);
                    crate::leanh::lean_dec(v_visited_583_);
                    if v___x_585_ == 0 {
                        v___x_586_ = lean_st_ref_take(v___y_569_);
                        v_visited_587_ = crate::leanh::lean_ctor_get(v___x_586_, 0);
                        v_localDecls_588_ = crate::leanh::lean_ctor_get(v___x_586_, 1);
                        v_extSigs_589_ = crate::leanh::lean_ctor_get(v___x_586_, 2);
                        v_isSharedCheck_678_ = (!crate::leanh::lean_is_exclusive(v___x_586_)) as u8;
                        if v_isSharedCheck_678_ == 0 {
                            v___x_591_ = v___x_586_;
                            v_isShared_592_ = v_isSharedCheck_678_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_extSigs_589_);
                            crate::leanh::lean_inc(v_localDecls_588_);
                            crate::leanh::lean_inc(v_visited_587_);
                            crate::leanh::lean_dec(v___x_586_);
                            v___x_591_ = crate::leanh::lean_box(0);
                            v_isShared_592_ = v_isSharedCheck_678_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_679_ = crate::leanh::lean_box(0);
                        v_a_574_ = v___x_679_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_680_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_680_, 0, v_b_568_);
                    return v___x_680_;
                }
            }
            1 => {
                v___x_575_ = 1usize;
                v___x_576_ = lean_usize_add(v_i_566_, v___x_575_);
                v_i_566_ = v___x_576_;
                v_b_568_ = v_a_574_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_579_) == 0 {
                    v_a_580_ = crate::leanh::lean_ctor_get(v___y_579_, 0);
                    crate::leanh::lean_inc(v_a_580_);
                    crate::leanh::lean_dec_ref_known(v___y_579_, 1);
                    v_a_574_ = v_a_580_;
                    state = 1;
                    continue;
                } else {
                    return v___y_579_;
                }
            }
            3 => {
                crate::leanh::lean_inc(v___x_584_);
                v___x_593_ = l_Lean_NameSet_insert(v_visited_587_, v___x_584_);
                if v_isShared_592_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_591_, 0, v___x_593_);
                    v___x_595_ = v___x_591_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_677_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_677_, 1, v_localDecls_588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_677_, 2, v_extSigs_589_);
                    v___x_595_ = v_reuseFailAlloc_677_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_596_ = lean_st_ref_set(v___y_569_, v___x_595_);
                v___x_597_ =
                    l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v___x_584_, v___y_571_);
                if crate::leanh::lean_obj_tag(v___x_597_) == 0 {
                    v_a_598_ = crate::leanh::lean_ctor_get(v___x_597_, 0);
                    crate::leanh::lean_inc(v_a_598_);
                    crate::leanh::lean_dec_ref_known(v___x_597_, 1);
                    if crate::leanh::lean_obj_tag(v_a_598_) == 1 {
                        v_val_599_ = crate::leanh::lean_ctor_get(v_a_598_, 0);
                        crate::leanh::lean_inc(v_val_599_);
                        crate::leanh::lean_dec_ref_known(v_a_598_, 1);
                        v___x_600_ = lean_st_ref_take(v___y_569_);
                        v_visited_601_ = crate::leanh::lean_ctor_get(v___x_600_, 0);
                        v_localDecls_602_ = crate::leanh::lean_ctor_get(v___x_600_, 1);
                        v_extSigs_603_ = crate::leanh::lean_ctor_get(v___x_600_, 2);
                        v_isSharedCheck_631_ = (!crate::leanh::lean_is_exclusive(v___x_600_)) as u8;
                        if v_isSharedCheck_631_ == 0 {
                            v___x_605_ = v___x_600_;
                            v_isShared_606_ = v_isSharedCheck_631_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_extSigs_603_);
                            crate::leanh::lean_inc(v_localDecls_602_);
                            crate::leanh::lean_inc(v_visited_601_);
                            crate::leanh::lean_dec(v___x_600_);
                            v___x_605_ = crate::leanh::lean_box(0);
                            v_isShared_606_ = v_isSharedCheck_631_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_598_);
                        crate::leanh::lean_inc(v___x_584_);
                        v___x_632_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(
                            v___x_584_, v___y_571_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_632_) == 0 {
                            v_a_633_ = crate::leanh::lean_ctor_get(v___x_632_, 0);
                            crate::leanh::lean_inc(v_a_633_);
                            crate::leanh::lean_dec_ref_known(v___x_632_, 1);
                            if crate::leanh::lean_obj_tag(v_a_633_) == 1 {
                                v_val_634_ = crate::leanh::lean_ctor_get(v_a_633_, 0);
                                crate::leanh::lean_inc(v_val_634_);
                                crate::leanh::lean_dec_ref_known(v_a_633_, 1);
                                v___x_635_ = lean_st_ref_take(v___y_569_);
                                v_visited_636_ = crate::leanh::lean_ctor_get(v___x_635_, 0);
                                v_localDecls_637_ = crate::leanh::lean_ctor_get(v___x_635_, 1);
                                v_extSigs_638_ = crate::leanh::lean_ctor_get(v___x_635_, 2);
                                v_isSharedCheck_648_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_635_)) as u8;
                                if v_isSharedCheck_648_ == 0 {
                                    v___x_640_ = v___x_635_;
                                    v_isShared_641_ = v_isSharedCheck_648_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_extSigs_638_);
                                    crate::leanh::lean_inc(v_localDecls_637_);
                                    crate::leanh::lean_inc(v_visited_636_);
                                    crate::leanh::lean_dec(v___x_635_);
                                    v___x_640_ = crate::leanh::lean_box(0);
                                    v_isShared_641_ = v_isSharedCheck_648_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_633_);
                                v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0;
                                v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1;
                                v___x_651_ = crate::leanh::lean_unsigned_to_nat(42);
                                v___x_652_ = crate::leanh::lean_unsigned_to_nat(8);
                                v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2;
                                v___x_654_ = 1;
                                crate::leanh::lean_inc(v___x_584_);
                                v___x_655_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_584_, v___x_654_);
                                v___x_656_ = lean_string_append(v___x_653_, v___x_655_);
                                crate::leanh::lean_dec_ref(v___x_655_);
                                v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3;
                                v___x_658_ = lean_string_append(v___x_656_, v___x_657_);
                                v___x_659_ = l_mkPanicMessageWithDecl(
                                    v___x_649_, v___x_650_, v___x_651_, v___x_652_, v___x_658_,
                                );
                                crate::leanh::lean_dec_ref(v___x_658_);
                                v___x_660_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v___x_659_, v___y_569_, v___y_570_, v___y_571_);
                                v___y_579_ = v___x_660_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_661_ = crate::leanh::lean_ctor_get(v___x_632_, 0);
                            v_isSharedCheck_668_ =
                                (!crate::leanh::lean_is_exclusive(v___x_632_)) as u8;
                            if v_isSharedCheck_668_ == 0 {
                                v___x_663_ = v___x_632_;
                                v_isShared_664_ = v_isSharedCheck_668_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_661_);
                                crate::leanh::lean_dec(v___x_632_);
                                v___x_663_ = crate::leanh::lean_box(0);
                                v_isShared_664_ = v_isSharedCheck_668_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_669_ = crate::leanh::lean_ctor_get(v___x_597_, 0);
                    v_isSharedCheck_676_ = (!crate::leanh::lean_is_exclusive(v___x_597_)) as u8;
                    if v_isSharedCheck_676_ == 0 {
                        v___x_671_ = v___x_597_;
                        v_isShared_672_ = v_isSharedCheck_676_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_669_);
                        crate::leanh::lean_dec(v___x_597_);
                        v___x_671_ = crate::leanh::lean_box(0);
                        v_isShared_672_ = v_isSharedCheck_676_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_val_599_);
                v___x_607_ = lean_array_push(v_localDecls_602_, v_val_599_);
                if v_isShared_606_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_605_, 1, v___x_607_);
                    v___x_609_ = v___x_605_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v_visited_601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 2, v_extSigs_603_);
                    v___x_609_ = v_reuseFailAlloc_630_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_610_ = lean_st_ref_set(v___y_569_, v___x_609_);
                v_toSignature_611_ = crate::leanh::lean_ctor_get(v_val_599_, 0);
                crate::leanh::lean_inc_ref(v_toSignature_611_);
                v_value_612_ = crate::leanh::lean_ctor_get(v_val_599_, 1);
                crate::leanh::lean_inc_ref(v_value_612_);
                crate::leanh::lean_dec(v_val_599_);
                v___x_613_ = 1;
                v___x_614_ = crate::leanh::lean_box((v___x_613_) as usize);
                v___f_615_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0___boxed as *mut core::ffi::c_void, 6, 1);
                crate::leanh::lean_closure_set(v___f_615_, 0, v___x_614_);
                v___x_616_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v___f_615_, v_value_612_, v___y_569_, v___y_570_, v___y_571_);
                if crate::leanh::lean_obj_tag(v___x_616_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_616_, 1);
                    v___x_617_ = lean_st_ref_get(v___y_571_);
                    v_env_626_ = crate::leanh::lean_ctor_get(v___x_617_, 0);
                    crate::leanh::lean_inc_ref_n(v_env_626_, 2);
                    crate::leanh::lean_dec(v___x_617_);
                    v_name_627_ = crate::leanh::lean_ctor_get(v_toSignature_611_, 0);
                    crate::leanh::lean_inc_n(v_name_627_, 2);
                    crate::leanh::lean_dec_ref(v_toSignature_611_);
                    v___x_628_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_626_, v_name_627_);
                    if crate::leanh::lean_obj_tag(v___x_628_) == 0 {
                        v___x_629_ = lean_get_init_fn_name_for(v_env_626_, v_name_627_);
                        v___y_619_ = v___x_629_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_name_627_);
                        crate::leanh::lean_dec_ref(v_env_626_);
                        v___y_619_ = v___x_628_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_toSignature_611_);
                    v___y_579_ = v___x_616_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_619_) == 1 {
                    v_val_620_ = crate::leanh::lean_ctor_get(v___y_619_, 0);
                    crate::leanh::lean_inc(v_val_620_);
                    crate::leanh::lean_dec_ref_known(v___y_619_, 1);
                    v___x_621_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_622_ = lean_mk_empty_array_with_capacity(v___x_621_);
                    v___x_623_ = lean_array_push(v___x_622_, v_val_620_);
                    v___x_624_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_623_, v___y_569_, v___y_570_, v___y_571_);
                    crate::leanh::lean_dec_ref(v___x_623_);
                    v___y_579_ = v___x_624_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_619_);
                    v___x_625_ = crate::leanh::lean_box(0);
                    v_a_574_ = v___x_625_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                v___x_642_ = lean_array_push(v_extSigs_638_, v_val_634_);
                if v_isShared_641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_640_, 2, v___x_642_);
                    v___x_644_ = v___x_640_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_647_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_647_, 0, v_visited_636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_647_, 1, v_localDecls_637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_647_, 2, v___x_642_);
                    v___x_644_ = v_reuseFailAlloc_647_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_645_ = lean_st_ref_set(v___y_569_, v___x_644_);
                v___x_646_ = crate::leanh::lean_box(0);
                v_a_574_ = v___x_646_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_664_ == 0 {
                    v___x_666_ = v___x_663_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_667_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
                    v___x_666_ = v_reuseFailAlloc_667_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_666_;
            }
            12 => {
                if v_isShared_672_ == 0 {
                    v___x_674_ = v___x_671_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
                    v___x_674_ = v_reuseFailAlloc_675_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(
    mut v_names_681_: *mut crate::leanh::LeanObject,
    mut v_a_682_: *mut crate::leanh::LeanObject,
    mut v_a_683_: *mut crate::leanh::LeanObject,
    mut v_a_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    v___x_686_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_687_ = lean_array_get_size(v_names_681_);
    v___x_688_ = crate::leanh::lean_box(0);
    v___x_689_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
    if v___x_689_ == 0 {
        let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_690_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_690_, 0, v___x_688_);
        return v___x_690_;
    } else {
        let mut v___x_691_: u8 = 0;
        v___x_691_ = lean_nat_dec_le(v___x_687_, v___x_687_);
        if v___x_691_ == 0 {
            if v___x_689_ == 0 {
                let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_692_, 0, v___x_688_);
                return v___x_692_;
            } else {
                let mut v___x_693_: usize = 0;
                let mut v___x_694_: usize = 0;
                let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_693_ = 0usize;
                v___x_694_ = lean_usize_of_nat(v___x_687_);
                v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_names_681_, v___x_693_, v___x_694_, v___x_688_, v_a_682_, v_a_683_, v_a_684_);
                return v___x_695_;
            }
        } else {
            let mut v___x_696_: usize = 0;
            let mut v___x_697_: usize = 0;
            let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_696_ = 0usize;
            v___x_697_ = lean_usize_of_nat(v___x_687_);
            v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_names_681_, v___x_696_, v___x_697_, v___x_688_, v_a_682_, v_a_683_, v_a_684_);
            return v___x_698_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(
    mut v_code_699_: *mut crate::leanh::LeanObject,
    mut v_a_700_: *mut crate::leanh::LeanObject,
    mut v_a_701_: *mut crate::leanh::LeanObject,
    mut v_a_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_code_699_) == 0 {
                    v_decl_713_ = crate::leanh::lean_ctor_get(v_code_699_, 0);
                    crate::leanh::lean_inc_ref(v_decl_713_);
                    crate::leanh::lean_dec_ref_known(v_code_699_, 2);
                    v_value_714_ = crate::leanh::lean_ctor_get(v_decl_713_, 3);
                    crate::leanh::lean_inc(v_value_714_);
                    crate::leanh::lean_dec_ref(v_decl_713_);
                    match crate::leanh::lean_obj_tag(v_value_714_) {
                        3 => {
                            v_declName_715_ = crate::leanh::lean_ctor_get(v_value_714_, 0);
                            crate::leanh::lean_inc(v_declName_715_);
                            crate::leanh::lean_dec_ref_known(v_value_714_, 3);
                            v___x_716_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_717_ = lean_mk_empty_array_with_capacity(v___x_716_);
                            v___x_718_ = lean_array_push(v___x_717_, v_declName_715_);
                            v___x_719_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_718_, v_a_700_, v_a_701_, v_a_702_);
                            crate::leanh::lean_dec_ref(v___x_718_);
                            return v___x_719_;
                        }
                        9 => {
                            v_fn_720_ = crate::leanh::lean_ctor_get(v_value_714_, 0);
                            crate::leanh::lean_inc(v_fn_720_);
                            crate::leanh::lean_dec_ref_known(v_value_714_, 2);
                            v_declName_705_ = v_fn_720_;
                            v___y_706_ = v_a_700_;
                            v___y_707_ = v_a_701_;
                            v___y_708_ = v_a_702_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_fn_721_ = crate::leanh::lean_ctor_get(v_value_714_, 0);
                            crate::leanh::lean_inc(v_fn_721_);
                            crate::leanh::lean_dec_ref_known(v_value_714_, 2);
                            v_declName_705_ = v_fn_721_;
                            v___y_706_ = v_a_700_;
                            v___y_707_ = v_a_701_;
                            v___y_708_ = v_a_702_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_value_714_);
                            v___x_722_ = crate::leanh::lean_box(0);
                            v___x_723_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_723_, 0, v___x_722_);
                            return v___x_723_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_code_699_);
                    v___x_724_ = crate::leanh::lean_box(0);
                    v___x_725_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_725_, 0, v___x_724_);
                    return v___x_725_;
                }
            }
            1 => {
                v___x_709_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_710_ = lean_mk_empty_array_with_capacity(v___x_709_);
                v___x_711_ = lean_array_push(v___x_710_, v_declName_705_);
                v___x_712_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_711_, v___y_706_, v___y_707_, v___y_708_);
                crate::leanh::lean_dec_ref(v___x_711_);
                return v___x_712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(
    mut v_pu_726_: u8,
    mut v_as_727_: *mut crate::leanh::LeanObject,
    mut v_i_728_: usize,
    mut v_stop_729_: usize,
    mut v_b_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
    mut v___y_732_: *mut crate::leanh::LeanObject,
    mut v___y_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: usize = 0;
    let mut v___x_739_: usize = 0;
    let mut v___x_741_: u8 = 0;
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_741_ = lean_usize_dec_eq(v_i_728_, v_stop_729_);
                if v___x_741_ == 0 {
                    v___x_742_ = lean_array_uget_borrowed(v_as_727_, v_i_728_);
                    match crate::leanh::lean_obj_tag(v___x_742_) {
                        0 => {
                            v_code_743_ = crate::leanh::lean_ctor_get(v___x_742_, 2);
                            crate::leanh::lean_inc_ref(v_code_743_);
                            v___x_744_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_726_, v_code_743_, v___y_731_, v___y_732_, v___y_733_);
                            v___y_736_ = v___x_744_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_745_ = crate::leanh::lean_ctor_get(v___x_742_, 1);
                            crate::leanh::lean_inc_ref(v_code_745_);
                            v___x_746_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_726_, v_code_745_, v___y_731_, v___y_732_, v___y_733_);
                            v___y_736_ = v___x_746_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_747_ = crate::leanh::lean_ctor_get(v___x_742_, 0);
                            crate::leanh::lean_inc_ref(v_code_747_);
                            v___x_748_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_726_, v_code_747_, v___y_731_, v___y_732_, v___y_733_);
                            v___y_736_ = v___x_748_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_749_, 0, v_b_730_);
                    return v___x_749_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_736_) == 0 {
                    v_a_737_ = crate::leanh::lean_ctor_get(v___y_736_, 0);
                    crate::leanh::lean_inc(v_a_737_);
                    crate::leanh::lean_dec_ref_known(v___y_736_, 1);
                    v___x_738_ = 1usize;
                    v___x_739_ = lean_usize_add(v_i_728_, v___x_738_);
                    v_i_728_ = v___x_739_;
                    v_b_730_ = v_a_737_;
                    state = 0;
                    continue;
                } else {
                    return v___y_736_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(
    mut v_pu_750_: u8,
    mut v_c_751_: *mut crate::leanh::LeanObject,
    mut v___y_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
    mut v___y_754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_759_: u8 = 0;
    let mut v_k_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: u8 = 0;
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: u8 = 0;
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: usize = 0;
    let mut v___x_786_: usize = 0;
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: usize = 0;
    let mut v___x_789_: usize = 0;
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_809_: u8 = 0;
    let mut v_unused_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_c_751_);
                v___x_756_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(v_c_751_, v___y_752_, v___y_753_, v___y_754_);
                if crate::leanh::lean_obj_tag(v___x_756_) == 0 {
                    v_isSharedCheck_809_ = (!crate::leanh::lean_is_exclusive(v___x_756_)) as u8;
                    if v_isSharedCheck_809_ == 0 {
                        v_unused_810_ = crate::leanh::lean_ctor_get(v___x_756_, 0);
                        crate::leanh::lean_dec(v_unused_810_);
                        v___x_758_ = v___x_756_;
                        v_isShared_759_ = v_isSharedCheck_809_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_756_);
                        v___x_758_ = crate::leanh::lean_box(0);
                        v_isShared_759_ = v_isSharedCheck_809_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_c_751_);
                    return v___x_756_;
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_c_751_) {
                0 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_k_760_ = crate::leanh::lean_ctor_get(v_c_751_, 1);
                    crate::leanh::lean_inc_ref(v_k_760_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 2);
                    v_c_751_ = v_k_760_;
                    state = 0;
                    continue;
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_decl_762_ = crate::leanh::lean_ctor_get(v_c_751_, 0);
                    crate::leanh::lean_inc_ref(v_decl_762_);
                    v_k_763_ = crate::leanh::lean_ctor_get(v_c_751_, 1);
                    crate::leanh::lean_inc_ref(v_k_763_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 2);
                    v_value_764_ = crate::leanh::lean_ctor_get(v_decl_762_, 4);
                    crate::leanh::lean_inc_ref(v_value_764_);
                    crate::leanh::lean_dec_ref(v_decl_762_);
                    v___x_765_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_750_, v_value_764_, v___y_752_, v___y_753_, v___y_754_);
                    if crate::leanh::lean_obj_tag(v___x_765_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_765_, 1);
                        v_c_751_ = v_k_763_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_763_);
                        return v___x_765_;
                    }
                }
                2 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_decl_767_ = crate::leanh::lean_ctor_get(v_c_751_, 0);
                    crate::leanh::lean_inc_ref(v_decl_767_);
                    v_k_768_ = crate::leanh::lean_ctor_get(v_c_751_, 1);
                    crate::leanh::lean_inc_ref(v_k_768_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 2);
                    v_value_769_ = crate::leanh::lean_ctor_get(v_decl_767_, 4);
                    crate::leanh::lean_inc_ref(v_value_769_);
                    crate::leanh::lean_dec_ref(v_decl_767_);
                    v___x_770_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_750_, v_value_769_, v___y_752_, v___y_753_, v___y_754_);
                    if crate::leanh::lean_obj_tag(v___x_770_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_770_, 1);
                        v_c_751_ = v_k_768_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_768_);
                        return v___x_770_;
                    }
                }
                4 => {
                    v_cases_772_ = crate::leanh::lean_ctor_get(v_c_751_, 0);
                    crate::leanh::lean_inc_ref(v_cases_772_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 1);
                    v_alts_773_ = crate::leanh::lean_ctor_get(v_cases_772_, 3);
                    crate::leanh::lean_inc_ref(v_alts_773_);
                    crate::leanh::lean_dec_ref(v_cases_772_);
                    v___x_774_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_775_ = lean_array_get_size(v_alts_773_);
                    v___x_776_ = crate::leanh::lean_box(0);
                    v___x_777_ = lean_nat_dec_lt(v___x_774_, v___x_775_);
                    if v___x_777_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_773_);
                        if v_isShared_759_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_758_, 0, v___x_776_);
                            v___x_779_ = v___x_758_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_780_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_776_);
                            v___x_779_ = v_reuseFailAlloc_780_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_781_ = lean_nat_dec_le(v___x_775_, v___x_775_);
                        if v___x_781_ == 0 {
                            if v___x_777_ == 0 {
                                crate::leanh::lean_dec_ref(v_alts_773_);
                                if v_isShared_759_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_758_, 0, v___x_776_);
                                    v___x_783_ = v___x_758_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_784_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_784_,
                                        0,
                                        v___x_776_,
                                    );
                                    v___x_783_ = v_reuseFailAlloc_784_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_758_);
                                v___x_785_ = 0usize;
                                v___x_786_ = lean_usize_of_nat(v___x_775_);
                                v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_750_, v_alts_773_, v___x_785_, v___x_786_, v___x_776_, v___y_752_, v___y_753_, v___y_754_);
                                crate::leanh::lean_dec_ref(v_alts_773_);
                                return v___x_787_;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_758_);
                            v___x_788_ = 0usize;
                            v___x_789_ = lean_usize_of_nat(v___x_775_);
                            v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_750_, v_alts_773_, v___x_788_, v___x_789_, v___x_776_, v___y_752_, v___y_753_, v___y_754_);
                            crate::leanh::lean_dec_ref(v_alts_773_);
                            return v___x_790_;
                        }
                    }
                }
                7 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_k_791_ = crate::leanh::lean_ctor_get(v_c_751_, 3);
                    crate::leanh::lean_inc_ref(v_k_791_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 4);
                    v_c_751_ = v_k_791_;
                    state = 0;
                    continue;
                }
                8 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_k_793_ = crate::leanh::lean_ctor_get(v_c_751_, 3);
                    crate::leanh::lean_inc_ref(v_k_793_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 4);
                    v_c_751_ = v_k_793_;
                    state = 0;
                    continue;
                }
                9 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_k_795_ = crate::leanh::lean_ctor_get(v_c_751_, 5);
                    crate::leanh::lean_inc_ref(v_k_795_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 6);
                    v_c_751_ = v_k_795_;
                    state = 0;
                    continue;
                }
                10 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_k_797_ = crate::leanh::lean_ctor_get(v_c_751_, 2);
                    crate::leanh::lean_inc_ref(v_k_797_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 3);
                    v_c_751_ = v_k_797_;
                    state = 0;
                    continue;
                }
                11 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_k_799_ = crate::leanh::lean_ctor_get(v_c_751_, 2);
                    crate::leanh::lean_inc_ref(v_k_799_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 3);
                    v_c_751_ = v_k_799_;
                    state = 0;
                    continue;
                }
                12 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_k_801_ = crate::leanh::lean_ctor_get(v_c_751_, 3);
                    crate::leanh::lean_inc_ref(v_k_801_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 4);
                    v_c_751_ = v_k_801_;
                    state = 0;
                    continue;
                }
                13 => {
                    crate::leanh::lean_del_object(v___x_758_);
                    v_k_803_ = crate::leanh::lean_ctor_get(v_c_751_, 1);
                    crate::leanh::lean_inc_ref(v_k_803_);
                    crate::leanh::lean_dec_ref_known(v_c_751_, 2);
                    v_c_751_ = v_k_803_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_c_751_);
                    v___x_805_ = crate::leanh::lean_box(0);
                    if v_isShared_759_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_758_, 0, v___x_805_);
                        v___x_807_ = v___x_758_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
                        v___x_807_ = v_reuseFailAlloc_808_;
                        state = 4;
                        continue;
                    }
                }
            },
            2 => {
                return v___x_779_;
            }
            3 => {
                return v___x_783_;
            }
            4 => {
                return v___x_807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(
    mut v___x_811_: u8,
    mut v_x_812_: *mut crate::leanh::LeanObject,
    mut v___y_813_: *mut crate::leanh::LeanObject,
    mut v___y_814_: *mut crate::leanh::LeanObject,
    mut v___y_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v___x_811_, v_x_812_, v___y_813_, v___y_814_, v___y_815_);
    return v___x_817_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1___boxed(
    mut v_pu_818_: *mut crate::leanh::LeanObject,
    mut v_as_819_: *mut crate::leanh::LeanObject,
    mut v_i_820_: *mut crate::leanh::LeanObject,
    mut v_stop_821_: *mut crate::leanh::LeanObject,
    mut v_b_822_: *mut crate::leanh::LeanObject,
    mut v___y_823_: *mut crate::leanh::LeanObject,
    mut v___y_824_: *mut crate::leanh::LeanObject,
    mut v___y_825_: *mut crate::leanh::LeanObject,
    mut v___y_826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_827_: u8 = 0;
    let mut v_i_boxed_828_: usize = 0;
    let mut v_stop_boxed_829_: usize = 0;
    let mut v_res_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_827_ = (crate::leanh::lean_unbox(v_pu_818_) as u8);
    v_i_boxed_828_ = crate::leanh::lean_unbox_usize(v_i_820_);
    crate::leanh::lean_dec(v_i_820_);
    v_stop_boxed_829_ = crate::leanh::lean_unbox_usize(v_stop_821_);
    crate::leanh::lean_dec(v_stop_821_);
    v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_boxed_827_, v_as_819_, v_i_boxed_828_, v_stop_boxed_829_, v_b_822_, v___y_823_, v___y_824_, v___y_825_);
    crate::leanh::lean_dec(v___y_825_);
    crate::leanh::lean_dec_ref(v___y_824_);
    crate::leanh::lean_dec(v___y_823_);
    crate::leanh::lean_dec_ref(v_as_819_);
    return v_res_830_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go___boxed(
    mut v_names_831_: *mut crate::leanh::LeanObject,
    mut v_a_832_: *mut crate::leanh::LeanObject,
    mut v_a_833_: *mut crate::leanh::LeanObject,
    mut v_a_834_: *mut crate::leanh::LeanObject,
    mut v_a_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_836_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(
        v_names_831_,
        v_a_832_,
        v_a_833_,
        v_a_834_,
    );
    crate::leanh::lean_dec(v_a_834_);
    crate::leanh::lean_dec_ref(v_a_833_);
    crate::leanh::lean_dec(v_a_832_);
    crate::leanh::lean_dec_ref(v_names_831_);
    return v_res_836_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode___boxed(
    mut v_code_837_: *mut crate::leanh::LeanObject,
    mut v_a_838_: *mut crate::leanh::LeanObject,
    mut v_a_839_: *mut crate::leanh::LeanObject,
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_a_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_842_ =
        l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(
            v_code_837_,
            v_a_838_,
            v_a_839_,
            v_a_840_,
        );
    crate::leanh::lean_dec(v_a_840_);
    crate::leanh::lean_dec_ref(v_a_839_);
    crate::leanh::lean_dec(v_a_838_);
    return v_res_842_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0___boxed(
    mut v_pu_843_: *mut crate::leanh::LeanObject,
    mut v_c_844_: *mut crate::leanh::LeanObject,
    mut v___y_845_: *mut crate::leanh::LeanObject,
    mut v___y_846_: *mut crate::leanh::LeanObject,
    mut v___y_847_: *mut crate::leanh::LeanObject,
    mut v___y_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_849_: u8 = 0;
    let mut v_res_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_849_ = (crate::leanh::lean_unbox(v_pu_843_) as u8);
    v_res_850_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_boxed_849_, v_c_844_, v___y_845_, v___y_846_, v___y_847_);
    crate::leanh::lean_dec(v___y_847_);
    crate::leanh::lean_dec_ref(v___y_846_);
    crate::leanh::lean_dec(v___y_845_);
    return v_res_850_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___boxed(
    mut v_as_851_: *mut crate::leanh::LeanObject,
    mut v_i_852_: *mut crate::leanh::LeanObject,
    mut v_stop_853_: *mut crate::leanh::LeanObject,
    mut v_b_854_: *mut crate::leanh::LeanObject,
    mut v___y_855_: *mut crate::leanh::LeanObject,
    mut v___y_856_: *mut crate::leanh::LeanObject,
    mut v___y_857_: *mut crate::leanh::LeanObject,
    mut v___y_858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_859_: usize = 0;
    let mut v_stop_boxed_860_: usize = 0;
    let mut v_res_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_859_ = crate::leanh::lean_unbox_usize(v_i_852_);
    crate::leanh::lean_dec(v_i_852_);
    v_stop_boxed_860_ = crate::leanh::lean_unbox_usize(v_stop_853_);
    crate::leanh::lean_dec(v_stop_853_);
    v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_as_851_, v_i_boxed_859_, v_stop_boxed_860_, v_b_854_, v___y_855_, v___y_856_, v___y_857_);
    crate::leanh::lean_dec(v___y_857_);
    crate::leanh::lean_dec_ref(v___y_856_);
    crate::leanh::lean_dec(v___y_855_);
    crate::leanh::lean_dec_ref(v_as_851_);
    return v_res_861_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(
    mut v_pu_862_: u8,
    mut v_f_863_: *mut crate::leanh::LeanObject,
    mut v_v_864_: *mut crate::leanh::LeanObject,
    mut v___y_865_: *mut crate::leanh::LeanObject,
    mut v___y_866_: *mut crate::leanh::LeanObject,
    mut v___y_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_863_, v_v_864_, v___y_865_, v___y_866_, v___y_867_);
    return v___x_869_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___boxed(
    mut v_pu_870_: *mut crate::leanh::LeanObject,
    mut v_f_871_: *mut crate::leanh::LeanObject,
    mut v_v_872_: *mut crate::leanh::LeanObject,
    mut v___y_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
    mut v___y_875_: *mut crate::leanh::LeanObject,
    mut v___y_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_877_: u8 = 0;
    let mut v_res_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_877_ = (crate::leanh::lean_unbox(v_pu_870_) as u8);
    v_res_878_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(v_pu_boxed_877_, v_f_871_, v_v_872_, v___y_873_, v___y_874_, v___y_875_);
    crate::leanh::lean_dec(v___y_875_);
    crate::leanh::lean_dec_ref(v___y_874_);
    crate::leanh::lean_dec(v___y_873_);
    return v_res_878_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = l_Lean_Compiler_LCNF_collectUsedDecls___closed__0;
    v___x_882_ = l_Lean_NameSet_empty;
    v___x_883_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_883_, 0, v___x_882_);
    crate::leanh::lean_ctor_set(v___x_883_, 1, v___x_881_);
    crate::leanh::lean_ctor_set(v___x_883_, 2, v___x_881_);
    return v___x_883_;
}
pub unsafe fn l_Lean_Compiler_LCNF_collectUsedDecls(
    mut v_decls_884_: *mut crate::leanh::LeanObject,
    mut v_a_885_: *mut crate::leanh::LeanObject,
    mut v_a_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localDecls_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extSigs_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_unused_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_906_: u8 = 0;
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_888_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_collectUsedDecls___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_collectUsedDecls___closed__1_once),
                    _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1,
                );
                v___x_889_ = lean_st_mk_ref(v___x_888_);
                v___x_890_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v_decls_884_, v___x_889_, v_a_885_, v_a_886_);
                if crate::leanh::lean_obj_tag(v___x_890_) == 0 {
                    v_isSharedCheck_901_ = (!crate::leanh::lean_is_exclusive(v___x_890_)) as u8;
                    if v_isSharedCheck_901_ == 0 {
                        v_unused_902_ = crate::leanh::lean_ctor_get(v___x_890_, 0);
                        crate::leanh::lean_dec(v_unused_902_);
                        v___x_892_ = v___x_890_;
                        v_isShared_893_ = v_isSharedCheck_901_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_890_);
                        v___x_892_ = crate::leanh::lean_box(0);
                        v_isShared_893_ = v_isSharedCheck_901_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_889_);
                    v_a_903_ = crate::leanh::lean_ctor_get(v___x_890_, 0);
                    v_isSharedCheck_910_ = (!crate::leanh::lean_is_exclusive(v___x_890_)) as u8;
                    if v_isSharedCheck_910_ == 0 {
                        v___x_905_ = v___x_890_;
                        v_isShared_906_ = v_isSharedCheck_910_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_903_);
                        crate::leanh::lean_dec(v___x_890_);
                        v___x_905_ = crate::leanh::lean_box(0);
                        v_isShared_906_ = v_isSharedCheck_910_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_894_ = lean_st_ref_get(v___x_889_);
                crate::leanh::lean_dec(v___x_889_);
                v_localDecls_895_ = crate::leanh::lean_ctor_get(v___x_894_, 1);
                crate::leanh::lean_inc_ref(v_localDecls_895_);
                v_extSigs_896_ = crate::leanh::lean_ctor_get(v___x_894_, 2);
                crate::leanh::lean_inc_ref(v_extSigs_896_);
                crate::leanh::lean_dec(v___x_894_);
                v___x_897_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_897_, 0, v_localDecls_895_);
                crate::leanh::lean_ctor_set(v___x_897_, 1, v_extSigs_896_);
                if v_isShared_893_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_892_, 0, v___x_897_);
                    v___x_899_ = v___x_892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
                    v___x_899_ = v_reuseFailAlloc_900_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_899_;
            }
            3 => {
                if v_isShared_906_ == 0 {
                    v___x_908_ = v___x_905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
                    v___x_908_ = v_reuseFailAlloc_909_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_collectUsedDecls___boxed(
    mut v_decls_911_: *mut crate::leanh::LeanObject,
    mut v_a_912_: *mut crate::leanh::LeanObject,
    mut v_a_913_: *mut crate::leanh::LeanObject,
    mut v_a_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_915_ = l_Lean_Compiler_LCNF_collectUsedDecls(v_decls_911_, v_a_912_, v_a_913_);
    crate::leanh::lean_dec(v_a_913_);
    crate::leanh::lean_dec_ref(v_a_912_);
    crate::leanh::lean_dec_ref(v_decls_911_);
    return v_res_915_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(
    mut v_modulePrefix_916_: *mut crate::leanh::LeanObject,
    mut v_as_917_: *mut crate::leanh::LeanObject,
    mut v_i_918_: usize,
    mut v_stop_919_: usize,
) -> u8 {
    let mut v___x_920_: u8 = 0;
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irPhases_923_: u8 = 0;
    let mut v___x_924_: u8 = 0;
    let mut v___y_926_: u8 = 0;
    let mut v___x_927_: usize = 0;
    let mut v___x_928_: usize = 0;
    let mut v___x_930_: u8 = 0;
    let mut v___x_931_: u8 = 0;
    let mut v_module_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: u8 = 0;
    let mut v___x_934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_920_ = lean_usize_dec_eq(v_i_918_, v_stop_919_);
                if v___x_920_ == 0 {
                    v___x_921_ = lean_array_uget_borrowed(v_as_917_, v_i_918_);
                    v_toImport_922_ = crate::leanh::lean_ctor_get(v___x_921_, 0);
                    v_irPhases_923_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_921_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_924_ = 1;
                    v___x_930_ = 1;
                    v___x_931_ = l_Lean_instBEqIRPhases_beq(v_irPhases_923_, v___x_930_);
                    if v___x_931_ == 0 {
                        v_module_932_ = crate::leanh::lean_ctor_get(v_toImport_922_, 0);
                        v___x_933_ = l_Lean_Name_isPrefixOf(v_modulePrefix_916_, v_module_932_);
                        v___y_926_ = v___x_933_;
                        state = 1;
                        continue;
                    } else {
                        v___y_926_ = v___x_920_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_934_ = 0;
                    return v___x_934_;
                }
            }
            1 => {
                if v___y_926_ == 0 {
                    v___x_927_ = 1usize;
                    v___x_928_ = lean_usize_add(v_i_918_, v___x_927_);
                    v_i_918_ = v___x_928_;
                    state = 0;
                    continue;
                } else {
                    return v___x_924_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0___boxed(
    mut v_modulePrefix_935_: *mut crate::leanh::LeanObject,
    mut v_as_936_: *mut crate::leanh::LeanObject,
    mut v_i_937_: *mut crate::leanh::LeanObject,
    mut v_stop_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_939_: usize = 0;
    let mut v_stop_boxed_940_: usize = 0;
    let mut v_res_941_: u8 = 0;
    let mut v_r_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_939_ = crate::leanh::lean_unbox_usize(v_i_937_);
    crate::leanh::lean_dec(v_i_937_);
    v_stop_boxed_940_ = crate::leanh::lean_unbox_usize(v_stop_938_);
    crate::leanh::lean_dec(v_stop_938_);
    v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_935_, v_as_936_, v_i_boxed_939_, v_stop_boxed_940_);
    crate::leanh::lean_dec_ref(v_as_936_);
    crate::leanh::lean_dec(v_modulePrefix_935_);
    v_r_942_ = crate::leanh::lean_box((v_res_941_) as usize);
    return v_r_942_;
}
pub unsafe fn l_Lean_Compiler_LCNF_usesModuleFrom(
    mut v_env_943_: *mut crate::leanh::LeanObject,
    mut v_modulePrefix_944_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: u8 = 0;
    v___x_945_ = l_Lean_Environment_header(v_env_943_);
    v_modules_946_ = crate::leanh::lean_ctor_get(v___x_945_, 3);
    crate::leanh::lean_inc_ref(v_modules_946_);
    crate::leanh::lean_dec_ref(v___x_945_);
    v___x_947_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_948_ = lean_array_get_size(v_modules_946_);
    v___x_949_ = lean_nat_dec_lt(v___x_947_, v___x_948_);
    if v___x_949_ == 0 {
        crate::leanh::lean_dec_ref(v_modules_946_);
        return v___x_949_;
    } else {
        if v___x_949_ == 0 {
            crate::leanh::lean_dec_ref(v_modules_946_);
            return v___x_949_;
        } else {
            let mut v___x_950_: usize = 0;
            let mut v___x_951_: usize = 0;
            let mut v___x_952_: u8 = 0;
            v___x_950_ = 0usize;
            v___x_951_ = lean_usize_of_nat(v___x_948_);
            v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_944_, v_modules_946_, v___x_950_, v___x_951_);
            crate::leanh::lean_dec_ref(v_modules_946_);
            return v___x_952_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_usesModuleFrom___boxed(
    mut v_env_953_: *mut crate::leanh::LeanObject,
    mut v_modulePrefix_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_955_: u8 = 0;
    let mut v_r_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_955_ = l_Lean_Compiler_LCNF_usesModuleFrom(v_env_953_, v_modulePrefix_954_);
    crate::leanh::lean_dec(v_modulePrefix_954_);
    crate::leanh::lean_dec_ref(v_env_953_);
    v_r_956_ = crate::leanh::lean_box((v_res_955_) as usize);
    return v_r_956_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_EmitUtil(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_EmitUtil(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_EmitUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_EmitUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_EmitUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_EmitUtil(builtin);
}
