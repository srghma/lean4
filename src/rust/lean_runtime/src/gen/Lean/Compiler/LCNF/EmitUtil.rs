// Lean compiler output
// Module: Lean.Compiler.LCNF.EmitUtil
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PhaseExt Lean.Compiler.InitAttr
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_4,
    lean_apply_5, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 109, 105, 116, 85, 116, 105, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1_value: LeanStringObject<78> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 109, 105, 116, 85, 116, 105, 108, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 99, 111, 108, 108, 101, 99, 116, 85, 115, 101, 100, 68, 101, 99, 108, 115, 46, 103, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2_value: LeanStringObject<64> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [99, 111, 108, 108, 101, 99, 116, 85, 115, 101, 100, 68, 101, 99, 108, 115, 58, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 111, 114, 32, 115, 105, 103, 110, 97, 116, 117, 114, 101, 32, 102, 111, 114, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_collectUsedDecls___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_collectUsedDecls___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_collectUsedDecls___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_collectUsedDecls___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_collectUsedDecls___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ = l_instMonadEIO(lean_box(0));
    return v___x_479_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(
    mut v_msg_482_: *mut LeanObject,
    mut v___y_483_: *mut LeanObject,
    mut v___y_484_: *mut LeanObject,
    mut v___y_485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v_toFunctor_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_499_: u8 = 0;
    let mut v___f_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823__overap_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut v_unused_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_521_: u8 = 0;
    let mut v_unused_522_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_487_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0);
                v___x_488_ = l_StateRefT_x27_instMonad___redArg(v___x_487_);
                v_toApplicative_489_ = lean_ctor_get(v___x_488_, 0);
                v_isSharedCheck_521_ = (!lean_is_exclusive(v___x_488_)) as u8;
                if v_isSharedCheck_521_ == 0 {
                    v_unused_522_ = lean_ctor_get(v___x_488_, 1);
                    lean_dec(v_unused_522_);
                    v___x_491_ = v___x_488_;
                    v_isShared_492_ = v_isSharedCheck_521_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_489_);
                    lean_dec(v___x_488_);
                    v___x_491_ = lean_box(0);
                    v_isShared_492_ = v_isSharedCheck_521_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_493_ = lean_ctor_get(v_toApplicative_489_, 0);
                v_toSeq_494_ = lean_ctor_get(v_toApplicative_489_, 2);
                v_toSeqLeft_495_ = lean_ctor_get(v_toApplicative_489_, 3);
                v_toSeqRight_496_ = lean_ctor_get(v_toApplicative_489_, 4);
                v_isSharedCheck_519_ = (!lean_is_exclusive(v_toApplicative_489_)) as u8;
                if v_isSharedCheck_519_ == 0 {
                    v_unused_520_ = lean_ctor_get(v_toApplicative_489_, 1);
                    lean_dec(v_unused_520_);
                    v___x_498_ = v_toApplicative_489_;
                    v_isShared_499_ = v_isSharedCheck_519_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_496_);
                    lean_inc(v_toSeqLeft_495_);
                    lean_inc(v_toSeq_494_);
                    lean_inc(v_toFunctor_493_);
                    lean_dec(v_toApplicative_489_);
                    v___x_498_ = lean_box(0);
                    v_isShared_499_ = v_isSharedCheck_519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_500_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1;
                v___f_501_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2;
                lean_inc_ref(v_toFunctor_493_);
                v___f_502_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_502_, 0, v_toFunctor_493_);
                v___f_503_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_503_, 0, v_toFunctor_493_);
                v___x_504_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_504_, 0, v___f_502_);
                lean_ctor_set(v___x_504_, 1, v___f_503_);
                v___f_505_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_505_, 0, v_toSeqRight_496_);
                v___f_506_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_506_, 0, v_toSeqLeft_495_);
                v___f_507_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_507_, 0, v_toSeq_494_);
                if v_isShared_499_ == 0 {
                    lean_ctor_set(v___x_498_, 4, v___f_505_);
                    lean_ctor_set(v___x_498_, 3, v___f_506_);
                    lean_ctor_set(v___x_498_, 2, v___f_507_);
                    lean_ctor_set(v___x_498_, 1, v___f_500_);
                    lean_ctor_set(v___x_498_, 0, v___x_504_);
                    v___x_509_ = v___x_498_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_504_);
                    lean_ctor_set(v_reuseFailAlloc_518_, 1, v___f_500_);
                    lean_ctor_set(v_reuseFailAlloc_518_, 2, v___f_507_);
                    lean_ctor_set(v_reuseFailAlloc_518_, 3, v___f_506_);
                    lean_ctor_set(v_reuseFailAlloc_518_, 4, v___f_505_);
                    v___x_509_ = v_reuseFailAlloc_518_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_492_ == 0 {
                    lean_ctor_set(v___x_491_, 1, v___f_501_);
                    lean_ctor_set(v___x_491_, 0, v___x_509_);
                    v___x_511_ = v___x_491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_509_);
                    lean_ctor_set(v_reuseFailAlloc_517_, 1, v___f_501_);
                    v___x_511_ = v_reuseFailAlloc_517_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_512_ = l_StateRefT_x27_instMonad___redArg(v___x_511_);
                v___x_513_ = lean_box(0);
                v___x_514_ = l_instInhabitedOfMonad___redArg(v___x_512_, v___x_513_);
                v___x_5823__overap_515_ = lean_panic_fn_borrowed(v___x_514_, v_msg_482_);
                lean_dec(v___x_514_);
                lean_inc(v___y_485_);
                lean_inc_ref(v___y_484_);
                lean_inc(v___y_483_);
                v___x_516_ = lean_apply_4(
                    v___x_5823__overap_515_,
                    v___y_483_,
                    v___y_484_,
                    v___y_485_,
                    lean_box(0),
                );
                return v___x_516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___boxed(
    mut v_msg_523_: *mut LeanObject,
    mut v___y_524_: *mut LeanObject,
    mut v___y_525_: *mut LeanObject,
    mut v___y_526_: *mut LeanObject,
    mut v___y_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_528_: *mut LeanObject = core::ptr::null_mut();
    v_res_528_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v_msg_523_, v___y_524_, v___y_525_, v___y_526_);
    lean_dec(v___y_526_);
    lean_dec_ref(v___y_525_);
    lean_dec(v___y_524_);
    return v_res_528_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(
    mut v_f_529_: *mut LeanObject,
    mut v_v_530_: *mut LeanObject,
    mut v___y_531_: *mut LeanObject,
    mut v___y_532_: *mut LeanObject,
    mut v___y_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_539_: u8 = 0;
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_544_: u8 = 0;
    let mut v_unused_545_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_530_) == 0 {
                    v_code_535_ = lean_ctor_get(v_v_530_, 0);
                    lean_inc_ref(v_code_535_);
                    lean_dec_ref_known(v_v_530_, 1);
                    lean_inc(v___y_533_);
                    lean_inc_ref(v___y_532_);
                    lean_inc(v___y_531_);
                    v___x_536_ = lean_apply_5(
                        v_f_529_,
                        v_code_535_,
                        v___y_531_,
                        v___y_532_,
                        v___y_533_,
                        lean_box(0),
                    );
                    return v___x_536_;
                } else {
                    lean_dec_ref(v_f_529_);
                    v_isSharedCheck_544_ = (!lean_is_exclusive(v_v_530_)) as u8;
                    if v_isSharedCheck_544_ == 0 {
                        v_unused_545_ = lean_ctor_get(v_v_530_, 0);
                        lean_dec(v_unused_545_);
                        v___x_538_ = v_v_530_;
                        v_isShared_539_ = v_isSharedCheck_544_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_530_);
                        v___x_538_ = lean_box(0);
                        v_isShared_539_ = v_isSharedCheck_544_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_540_ = lean_box(0);
                if v_isShared_539_ == 0 {
                    lean_ctor_set_tag(v___x_538_, 0);
                    lean_ctor_set(v___x_538_, 0, v___x_540_);
                    v___x_542_ = v___x_538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
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
    mut v_f_546_: *mut LeanObject,
    mut v_v_547_: *mut LeanObject,
    mut v___y_548_: *mut LeanObject,
    mut v___y_549_: *mut LeanObject,
    mut v___y_550_: *mut LeanObject,
    mut v___y_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_552_: *mut LeanObject = core::ptr::null_mut();
    v_res_552_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_546_, v_v_547_, v___y_548_, v___y_549_, v___y_550_);
    lean_dec(v___y_550_);
    lean_dec_ref(v___y_549_);
    lean_dec(v___y_548_);
    return v_res_552_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0___boxed(
    mut v___x_553_: *mut LeanObject,
    mut v_x_554_: *mut LeanObject,
    mut v___y_555_: *mut LeanObject,
    mut v___y_556_: *mut LeanObject,
    mut v___y_557_: *mut LeanObject,
    mut v___y_558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6627__boxed_559_: u8 = 0;
    let mut v_res_560_: *mut LeanObject = core::ptr::null_mut();
    v___x_6627__boxed_559_ = (lean_unbox(v___x_553_) as u8);
    v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(v___x_6627__boxed_559_, v_x_554_, v___y_555_, v___y_556_, v___y_557_);
    lean_dec(v___y_557_);
    lean_dec_ref(v___y_556_);
    lean_dec(v___y_555_);
    return v_res_560_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(
    mut v_as_565_: *mut LeanObject,
    mut v_i_566_: usize,
    mut v_stop_567_: usize,
    mut v_b_568_: *mut LeanObject,
    mut v___y_569_: *mut LeanObject,
    mut v___y_570_: *mut LeanObject,
    mut v___y_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: usize = 0;
    let mut v___x_576_: usize = 0;
    let mut v___y_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localDecls_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extSigs_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_592_: u8 = 0;
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localDecls_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extSigs_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_606_: u8 = 0;
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: u8 = 0;
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localDecls_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extSigs_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_648_: u8 = 0;
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_664_: u8 = 0;
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut v_a_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_672_: u8 = 0;
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_676_: u8 = 0;
    let mut v_reuseFailAlloc_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_678_: u8 = 0;
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_581_ = lean_usize_dec_eq(v_i_566_, v_stop_567_);
                if v___x_581_ == 0 {
                    v___x_582_ = lean_st_ref_get(v___y_569_);
                    v_visited_583_ = lean_ctor_get(v___x_582_, 0);
                    lean_inc(v_visited_583_);
                    lean_dec(v___x_582_);
                    v___x_584_ = lean_array_uget_borrowed(v_as_565_, v_i_566_);
                    v___x_585_ = l_Lean_NameSet_contains(v_visited_583_, v___x_584_);
                    lean_dec(v_visited_583_);
                    if v___x_585_ == 0 {
                        v___x_586_ = lean_st_ref_take(v___y_569_);
                        v_visited_587_ = lean_ctor_get(v___x_586_, 0);
                        v_localDecls_588_ = lean_ctor_get(v___x_586_, 1);
                        v_extSigs_589_ = lean_ctor_get(v___x_586_, 2);
                        v_isSharedCheck_678_ = (!lean_is_exclusive(v___x_586_)) as u8;
                        if v_isSharedCheck_678_ == 0 {
                            v___x_591_ = v___x_586_;
                            v_isShared_592_ = v_isSharedCheck_678_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_extSigs_589_);
                            lean_inc(v_localDecls_588_);
                            lean_inc(v_visited_587_);
                            lean_dec(v___x_586_);
                            v___x_591_ = lean_box(0);
                            v_isShared_592_ = v_isSharedCheck_678_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_679_ = lean_box(0);
                        v_a_574_ = v___x_679_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_680_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_680_, 0, v_b_568_);
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
                if lean_obj_tag(v___y_579_) == 0 {
                    v_a_580_ = lean_ctor_get(v___y_579_, 0);
                    lean_inc(v_a_580_);
                    lean_dec_ref_known(v___y_579_, 1);
                    v_a_574_ = v_a_580_;
                    state = 1;
                    continue;
                } else {
                    return v___y_579_;
                }
            }
            3 => {
                lean_inc(v___x_584_);
                v___x_593_ = l_Lean_NameSet_insert(v_visited_587_, v___x_584_);
                if v_isShared_592_ == 0 {
                    lean_ctor_set(v___x_591_, 0, v___x_593_);
                    v___x_595_ = v___x_591_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_593_);
                    lean_ctor_set(v_reuseFailAlloc_677_, 1, v_localDecls_588_);
                    lean_ctor_set(v_reuseFailAlloc_677_, 2, v_extSigs_589_);
                    v___x_595_ = v_reuseFailAlloc_677_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_596_ = lean_st_ref_set(v___y_569_, v___x_595_);
                v___x_597_ =
                    l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v___x_584_, v___y_571_);
                if lean_obj_tag(v___x_597_) == 0 {
                    v_a_598_ = lean_ctor_get(v___x_597_, 0);
                    lean_inc(v_a_598_);
                    lean_dec_ref_known(v___x_597_, 1);
                    if lean_obj_tag(v_a_598_) == 1 {
                        v_val_599_ = lean_ctor_get(v_a_598_, 0);
                        lean_inc(v_val_599_);
                        lean_dec_ref_known(v_a_598_, 1);
                        v___x_600_ = lean_st_ref_take(v___y_569_);
                        v_visited_601_ = lean_ctor_get(v___x_600_, 0);
                        v_localDecls_602_ = lean_ctor_get(v___x_600_, 1);
                        v_extSigs_603_ = lean_ctor_get(v___x_600_, 2);
                        v_isSharedCheck_631_ = (!lean_is_exclusive(v___x_600_)) as u8;
                        if v_isSharedCheck_631_ == 0 {
                            v___x_605_ = v___x_600_;
                            v_isShared_606_ = v_isSharedCheck_631_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_extSigs_603_);
                            lean_inc(v_localDecls_602_);
                            lean_inc(v_visited_601_);
                            lean_dec(v___x_600_);
                            v___x_605_ = lean_box(0);
                            v_isShared_606_ = v_isSharedCheck_631_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_598_);
                        lean_inc(v___x_584_);
                        v___x_632_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(
                            v___x_584_, v___y_571_,
                        );
                        if lean_obj_tag(v___x_632_) == 0 {
                            v_a_633_ = lean_ctor_get(v___x_632_, 0);
                            lean_inc(v_a_633_);
                            lean_dec_ref_known(v___x_632_, 1);
                            if lean_obj_tag(v_a_633_) == 1 {
                                v_val_634_ = lean_ctor_get(v_a_633_, 0);
                                lean_inc(v_val_634_);
                                lean_dec_ref_known(v_a_633_, 1);
                                v___x_635_ = lean_st_ref_take(v___y_569_);
                                v_visited_636_ = lean_ctor_get(v___x_635_, 0);
                                v_localDecls_637_ = lean_ctor_get(v___x_635_, 1);
                                v_extSigs_638_ = lean_ctor_get(v___x_635_, 2);
                                v_isSharedCheck_648_ = (!lean_is_exclusive(v___x_635_)) as u8;
                                if v_isSharedCheck_648_ == 0 {
                                    v___x_640_ = v___x_635_;
                                    v_isShared_641_ = v_isSharedCheck_648_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_extSigs_638_);
                                    lean_inc(v_localDecls_637_);
                                    lean_inc(v_visited_636_);
                                    lean_dec(v___x_635_);
                                    v___x_640_ = lean_box(0);
                                    v_isShared_641_ = v_isSharedCheck_648_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_633_);
                                v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0;
                                v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1;
                                v___x_651_ = lean_unsigned_to_nat(42);
                                v___x_652_ = lean_unsigned_to_nat(8);
                                v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2;
                                v___x_654_ = 1;
                                lean_inc(v___x_584_);
                                v___x_655_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_584_, v___x_654_);
                                v___x_656_ = lean_string_append(v___x_653_, v___x_655_);
                                lean_dec_ref(v___x_655_);
                                v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3;
                                v___x_658_ = lean_string_append(v___x_656_, v___x_657_);
                                v___x_659_ = l_mkPanicMessageWithDecl(
                                    v___x_649_, v___x_650_, v___x_651_, v___x_652_, v___x_658_,
                                );
                                lean_dec_ref(v___x_658_);
                                v___x_660_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v___x_659_, v___y_569_, v___y_570_, v___y_571_);
                                v___y_579_ = v___x_660_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_661_ = lean_ctor_get(v___x_632_, 0);
                            v_isSharedCheck_668_ = (!lean_is_exclusive(v___x_632_)) as u8;
                            if v_isSharedCheck_668_ == 0 {
                                v___x_663_ = v___x_632_;
                                v_isShared_664_ = v_isSharedCheck_668_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_661_);
                                lean_dec(v___x_632_);
                                v___x_663_ = lean_box(0);
                                v_isShared_664_ = v_isSharedCheck_668_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_669_ = lean_ctor_get(v___x_597_, 0);
                    v_isSharedCheck_676_ = (!lean_is_exclusive(v___x_597_)) as u8;
                    if v_isSharedCheck_676_ == 0 {
                        v___x_671_ = v___x_597_;
                        v_isShared_672_ = v_isSharedCheck_676_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_669_);
                        lean_dec(v___x_597_);
                        v___x_671_ = lean_box(0);
                        v_isShared_672_ = v_isSharedCheck_676_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_val_599_);
                v___x_607_ = lean_array_push(v_localDecls_602_, v_val_599_);
                if v_isShared_606_ == 0 {
                    lean_ctor_set(v___x_605_, 1, v___x_607_);
                    v___x_609_ = v___x_605_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_630_, 0, v_visited_601_);
                    lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_607_);
                    lean_ctor_set(v_reuseFailAlloc_630_, 2, v_extSigs_603_);
                    v___x_609_ = v_reuseFailAlloc_630_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_610_ = lean_st_ref_set(v___y_569_, v___x_609_);
                v_toSignature_611_ = lean_ctor_get(v_val_599_, 0);
                lean_inc_ref(v_toSignature_611_);
                v_value_612_ = lean_ctor_get(v_val_599_, 1);
                lean_inc_ref(v_value_612_);
                lean_dec(v_val_599_);
                v___x_613_ = 1;
                v___x_614_ = lean_box((v___x_613_) as usize);
                v___f_615_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0___boxed as *mut core::ffi::c_void, 6, 1);
                lean_closure_set(v___f_615_, 0, v___x_614_);
                v___x_616_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v___f_615_, v_value_612_, v___y_569_, v___y_570_, v___y_571_);
                if lean_obj_tag(v___x_616_) == 0 {
                    lean_dec_ref_known(v___x_616_, 1);
                    v___x_617_ = lean_st_ref_get(v___y_571_);
                    v_env_626_ = lean_ctor_get(v___x_617_, 0);
                    lean_inc_ref_n(v_env_626_, 2);
                    lean_dec(v___x_617_);
                    v_name_627_ = lean_ctor_get(v_toSignature_611_, 0);
                    lean_inc_n(v_name_627_, 2);
                    lean_dec_ref(v_toSignature_611_);
                    v___x_628_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_626_, v_name_627_);
                    if lean_obj_tag(v___x_628_) == 0 {
                        v___x_629_ = lean_get_init_fn_name_for(v_env_626_, v_name_627_);
                        v___y_619_ = v___x_629_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v_name_627_);
                        lean_dec_ref(v_env_626_);
                        v___y_619_ = v___x_628_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_toSignature_611_);
                    v___y_579_ = v___x_616_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                if lean_obj_tag(v___y_619_) == 1 {
                    v_val_620_ = lean_ctor_get(v___y_619_, 0);
                    lean_inc(v_val_620_);
                    lean_dec_ref_known(v___y_619_, 1);
                    v___x_621_ = lean_unsigned_to_nat(1);
                    v___x_622_ = lean_mk_empty_array_with_capacity(v___x_621_);
                    v___x_623_ = lean_array_push(v___x_622_, v_val_620_);
                    v___x_624_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_623_, v___y_569_, v___y_570_, v___y_571_);
                    lean_dec_ref(v___x_623_);
                    v___y_579_ = v___x_624_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_619_);
                    v___x_625_ = lean_box(0);
                    v_a_574_ = v___x_625_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                v___x_642_ = lean_array_push(v_extSigs_638_, v_val_634_);
                if v_isShared_641_ == 0 {
                    lean_ctor_set(v___x_640_, 2, v___x_642_);
                    v___x_644_ = v___x_640_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_647_, 0, v_visited_636_);
                    lean_ctor_set(v_reuseFailAlloc_647_, 1, v_localDecls_637_);
                    lean_ctor_set(v_reuseFailAlloc_647_, 2, v___x_642_);
                    v___x_644_ = v_reuseFailAlloc_647_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_645_ = lean_st_ref_set(v___y_569_, v___x_644_);
                v___x_646_ = lean_box(0);
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
                    v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
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
                    v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
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
    mut v_names_681_: *mut LeanObject,
    mut v_a_682_: *mut LeanObject,
    mut v_a_683_: *mut LeanObject,
    mut v_a_684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    v___x_686_ = lean_unsigned_to_nat(0);
    v___x_687_ = lean_array_get_size(v_names_681_);
    v___x_688_ = lean_box(0);
    v___x_689_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
    if v___x_689_ == 0 {
        let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
        v___x_690_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_690_, 0, v___x_688_);
        return v___x_690_;
    } else {
        let mut v___x_691_: u8 = 0;
        v___x_691_ = lean_nat_dec_le(v___x_687_, v___x_687_);
        if v___x_691_ == 0 {
            if v___x_689_ == 0 {
                let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
                v___x_692_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_692_, 0, v___x_688_);
                return v___x_692_;
            } else {
                let mut v___x_693_: usize = 0;
                let mut v___x_694_: usize = 0;
                let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
                v___x_693_ = 0usize;
                v___x_694_ = lean_usize_of_nat(v___x_687_);
                v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_names_681_, v___x_693_, v___x_694_, v___x_688_, v_a_682_, v_a_683_, v_a_684_);
                return v___x_695_;
            }
        } else {
            let mut v___x_696_: usize = 0;
            let mut v___x_697_: usize = 0;
            let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
            v___x_696_ = 0usize;
            v___x_697_ = lean_usize_of_nat(v___x_687_);
            v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_names_681_, v___x_696_, v___x_697_, v___x_688_, v_a_682_, v_a_683_, v_a_684_);
            return v___x_698_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(
    mut v_code_699_: *mut LeanObject,
    mut v_a_700_: *mut LeanObject,
    mut v_a_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_code_699_) == 0 {
                    v_decl_713_ = lean_ctor_get(v_code_699_, 0);
                    lean_inc_ref(v_decl_713_);
                    lean_dec_ref_known(v_code_699_, 2);
                    v_value_714_ = lean_ctor_get(v_decl_713_, 3);
                    lean_inc(v_value_714_);
                    lean_dec_ref(v_decl_713_);
                    match lean_obj_tag(v_value_714_) {
                        3 => {
                            v_declName_715_ = lean_ctor_get(v_value_714_, 0);
                            lean_inc(v_declName_715_);
                            lean_dec_ref_known(v_value_714_, 3);
                            v___x_716_ = lean_unsigned_to_nat(1);
                            v___x_717_ = lean_mk_empty_array_with_capacity(v___x_716_);
                            v___x_718_ = lean_array_push(v___x_717_, v_declName_715_);
                            v___x_719_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_718_, v_a_700_, v_a_701_, v_a_702_);
                            lean_dec_ref(v___x_718_);
                            return v___x_719_;
                        }
                        9 => {
                            v_fn_720_ = lean_ctor_get(v_value_714_, 0);
                            lean_inc(v_fn_720_);
                            lean_dec_ref_known(v_value_714_, 2);
                            v_declName_705_ = v_fn_720_;
                            v___y_706_ = v_a_700_;
                            v___y_707_ = v_a_701_;
                            v___y_708_ = v_a_702_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_fn_721_ = lean_ctor_get(v_value_714_, 0);
                            lean_inc(v_fn_721_);
                            lean_dec_ref_known(v_value_714_, 2);
                            v_declName_705_ = v_fn_721_;
                            v___y_706_ = v_a_700_;
                            v___y_707_ = v_a_701_;
                            v___y_708_ = v_a_702_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            lean_dec(v_value_714_);
                            v___x_722_ = lean_box(0);
                            v___x_723_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_723_, 0, v___x_722_);
                            return v___x_723_;
                        }
                    }
                } else {
                    lean_dec_ref(v_code_699_);
                    v___x_724_ = lean_box(0);
                    v___x_725_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_725_, 0, v___x_724_);
                    return v___x_725_;
                }
            }
            1 => {
                v___x_709_ = lean_unsigned_to_nat(1);
                v___x_710_ = lean_mk_empty_array_with_capacity(v___x_709_);
                v___x_711_ = lean_array_push(v___x_710_, v_declName_705_);
                v___x_712_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_711_, v___y_706_, v___y_707_, v___y_708_);
                lean_dec_ref(v___x_711_);
                return v___x_712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(
    mut v_pu_726_: u8,
    mut v_as_727_: *mut LeanObject,
    mut v_i_728_: usize,
    mut v_stop_729_: usize,
    mut v_b_730_: *mut LeanObject,
    mut v___y_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: usize = 0;
    let mut v___x_739_: usize = 0;
    let mut v___x_741_: u8 = 0;
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_741_ = lean_usize_dec_eq(v_i_728_, v_stop_729_);
                if v___x_741_ == 0 {
                    v___x_742_ = lean_array_uget_borrowed(v_as_727_, v_i_728_);
                    match lean_obj_tag(v___x_742_) {
                        0 => {
                            v_code_743_ = lean_ctor_get(v___x_742_, 2);
                            lean_inc_ref(v_code_743_);
                            v___x_744_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_726_, v_code_743_, v___y_731_, v___y_732_, v___y_733_);
                            v___y_736_ = v___x_744_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_745_ = lean_ctor_get(v___x_742_, 1);
                            lean_inc_ref(v_code_745_);
                            v___x_746_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_726_, v_code_745_, v___y_731_, v___y_732_, v___y_733_);
                            v___y_736_ = v___x_746_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_747_ = lean_ctor_get(v___x_742_, 0);
                            lean_inc_ref(v_code_747_);
                            v___x_748_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_726_, v_code_747_, v___y_731_, v___y_732_, v___y_733_);
                            v___y_736_ = v___x_748_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_749_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_749_, 0, v_b_730_);
                    return v___x_749_;
                }
            }
            1 => {
                if lean_obj_tag(v___y_736_) == 0 {
                    v_a_737_ = lean_ctor_get(v___y_736_, 0);
                    lean_inc(v_a_737_);
                    lean_dec_ref_known(v___y_736_, 1);
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
    mut v_c_751_: *mut LeanObject,
    mut v___y_752_: *mut LeanObject,
    mut v___y_753_: *mut LeanObject,
    mut v___y_754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_759_: u8 = 0;
    let mut v_k_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: u8 = 0;
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: u8 = 0;
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: usize = 0;
    let mut v___x_786_: usize = 0;
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: usize = 0;
    let mut v___x_789_: usize = 0;
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_809_: u8 = 0;
    let mut v_unused_810_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_c_751_);
                v___x_756_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(v_c_751_, v___y_752_, v___y_753_, v___y_754_);
                if lean_obj_tag(v___x_756_) == 0 {
                    v_isSharedCheck_809_ = (!lean_is_exclusive(v___x_756_)) as u8;
                    if v_isSharedCheck_809_ == 0 {
                        v_unused_810_ = lean_ctor_get(v___x_756_, 0);
                        lean_dec(v_unused_810_);
                        v___x_758_ = v___x_756_;
                        v_isShared_759_ = v_isSharedCheck_809_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_756_);
                        v___x_758_ = lean_box(0);
                        v_isShared_759_ = v_isSharedCheck_809_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_c_751_);
                    return v___x_756_;
                }
            }
            1 => match lean_obj_tag(v_c_751_) {
                0 => {
                    lean_del_object(v___x_758_);
                    v_k_760_ = lean_ctor_get(v_c_751_, 1);
                    lean_inc_ref(v_k_760_);
                    lean_dec_ref_known(v_c_751_, 2);
                    v_c_751_ = v_k_760_;
                    state = 0;
                    continue;
                }
                1 => {
                    lean_del_object(v___x_758_);
                    v_decl_762_ = lean_ctor_get(v_c_751_, 0);
                    lean_inc_ref(v_decl_762_);
                    v_k_763_ = lean_ctor_get(v_c_751_, 1);
                    lean_inc_ref(v_k_763_);
                    lean_dec_ref_known(v_c_751_, 2);
                    v_value_764_ = lean_ctor_get(v_decl_762_, 4);
                    lean_inc_ref(v_value_764_);
                    lean_dec_ref(v_decl_762_);
                    v___x_765_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_750_, v_value_764_, v___y_752_, v___y_753_, v___y_754_);
                    if lean_obj_tag(v___x_765_) == 0 {
                        lean_dec_ref_known(v___x_765_, 1);
                        v_c_751_ = v_k_763_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_763_);
                        return v___x_765_;
                    }
                }
                2 => {
                    lean_del_object(v___x_758_);
                    v_decl_767_ = lean_ctor_get(v_c_751_, 0);
                    lean_inc_ref(v_decl_767_);
                    v_k_768_ = lean_ctor_get(v_c_751_, 1);
                    lean_inc_ref(v_k_768_);
                    lean_dec_ref_known(v_c_751_, 2);
                    v_value_769_ = lean_ctor_get(v_decl_767_, 4);
                    lean_inc_ref(v_value_769_);
                    lean_dec_ref(v_decl_767_);
                    v___x_770_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_750_, v_value_769_, v___y_752_, v___y_753_, v___y_754_);
                    if lean_obj_tag(v___x_770_) == 0 {
                        lean_dec_ref_known(v___x_770_, 1);
                        v_c_751_ = v_k_768_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_768_);
                        return v___x_770_;
                    }
                }
                4 => {
                    v_cases_772_ = lean_ctor_get(v_c_751_, 0);
                    lean_inc_ref(v_cases_772_);
                    lean_dec_ref_known(v_c_751_, 1);
                    v_alts_773_ = lean_ctor_get(v_cases_772_, 3);
                    lean_inc_ref(v_alts_773_);
                    lean_dec_ref(v_cases_772_);
                    v___x_774_ = lean_unsigned_to_nat(0);
                    v___x_775_ = lean_array_get_size(v_alts_773_);
                    v___x_776_ = lean_box(0);
                    v___x_777_ = lean_nat_dec_lt(v___x_774_, v___x_775_);
                    if v___x_777_ == 0 {
                        lean_dec_ref(v_alts_773_);
                        if v_isShared_759_ == 0 {
                            lean_ctor_set(v___x_758_, 0, v___x_776_);
                            v___x_779_ = v___x_758_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_776_);
                            v___x_779_ = v_reuseFailAlloc_780_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_781_ = lean_nat_dec_le(v___x_775_, v___x_775_);
                        if v___x_781_ == 0 {
                            if v___x_777_ == 0 {
                                lean_dec_ref(v_alts_773_);
                                if v_isShared_759_ == 0 {
                                    lean_ctor_set(v___x_758_, 0, v___x_776_);
                                    v___x_783_ = v___x_758_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_776_);
                                    v___x_783_ = v_reuseFailAlloc_784_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_758_);
                                v___x_785_ = 0usize;
                                v___x_786_ = lean_usize_of_nat(v___x_775_);
                                v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_750_, v_alts_773_, v___x_785_, v___x_786_, v___x_776_, v___y_752_, v___y_753_, v___y_754_);
                                lean_dec_ref(v_alts_773_);
                                return v___x_787_;
                            }
                        } else {
                            lean_del_object(v___x_758_);
                            v___x_788_ = 0usize;
                            v___x_789_ = lean_usize_of_nat(v___x_775_);
                            v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_750_, v_alts_773_, v___x_788_, v___x_789_, v___x_776_, v___y_752_, v___y_753_, v___y_754_);
                            lean_dec_ref(v_alts_773_);
                            return v___x_790_;
                        }
                    }
                }
                7 => {
                    lean_del_object(v___x_758_);
                    v_k_791_ = lean_ctor_get(v_c_751_, 3);
                    lean_inc_ref(v_k_791_);
                    lean_dec_ref_known(v_c_751_, 4);
                    v_c_751_ = v_k_791_;
                    state = 0;
                    continue;
                }
                8 => {
                    lean_del_object(v___x_758_);
                    v_k_793_ = lean_ctor_get(v_c_751_, 3);
                    lean_inc_ref(v_k_793_);
                    lean_dec_ref_known(v_c_751_, 4);
                    v_c_751_ = v_k_793_;
                    state = 0;
                    continue;
                }
                9 => {
                    lean_del_object(v___x_758_);
                    v_k_795_ = lean_ctor_get(v_c_751_, 5);
                    lean_inc_ref(v_k_795_);
                    lean_dec_ref_known(v_c_751_, 6);
                    v_c_751_ = v_k_795_;
                    state = 0;
                    continue;
                }
                10 => {
                    lean_del_object(v___x_758_);
                    v_k_797_ = lean_ctor_get(v_c_751_, 2);
                    lean_inc_ref(v_k_797_);
                    lean_dec_ref_known(v_c_751_, 3);
                    v_c_751_ = v_k_797_;
                    state = 0;
                    continue;
                }
                11 => {
                    lean_del_object(v___x_758_);
                    v_k_799_ = lean_ctor_get(v_c_751_, 2);
                    lean_inc_ref(v_k_799_);
                    lean_dec_ref_known(v_c_751_, 3);
                    v_c_751_ = v_k_799_;
                    state = 0;
                    continue;
                }
                12 => {
                    lean_del_object(v___x_758_);
                    v_k_801_ = lean_ctor_get(v_c_751_, 3);
                    lean_inc_ref(v_k_801_);
                    lean_dec_ref_known(v_c_751_, 4);
                    v_c_751_ = v_k_801_;
                    state = 0;
                    continue;
                }
                13 => {
                    lean_del_object(v___x_758_);
                    v_k_803_ = lean_ctor_get(v_c_751_, 1);
                    lean_inc_ref(v_k_803_);
                    lean_dec_ref_known(v_c_751_, 2);
                    v_c_751_ = v_k_803_;
                    state = 0;
                    continue;
                }
                _ => {
                    lean_dec_ref(v_c_751_);
                    v___x_805_ = lean_box(0);
                    if v_isShared_759_ == 0 {
                        lean_ctor_set(v___x_758_, 0, v___x_805_);
                        v___x_807_ = v___x_758_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
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
    mut v_x_812_: *mut LeanObject,
    mut v___y_813_: *mut LeanObject,
    mut v___y_814_: *mut LeanObject,
    mut v___y_815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    v___x_817_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v___x_811_, v_x_812_, v___y_813_, v___y_814_, v___y_815_);
    return v___x_817_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1___boxed(
    mut v_pu_818_: *mut LeanObject,
    mut v_as_819_: *mut LeanObject,
    mut v_i_820_: *mut LeanObject,
    mut v_stop_821_: *mut LeanObject,
    mut v_b_822_: *mut LeanObject,
    mut v___y_823_: *mut LeanObject,
    mut v___y_824_: *mut LeanObject,
    mut v___y_825_: *mut LeanObject,
    mut v___y_826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_827_: u8 = 0;
    let mut v_i_boxed_828_: usize = 0;
    let mut v_stop_boxed_829_: usize = 0;
    let mut v_res_830_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_827_ = (lean_unbox(v_pu_818_) as u8);
    v_i_boxed_828_ = lean_unbox_usize(v_i_820_);
    lean_dec(v_i_820_);
    v_stop_boxed_829_ = lean_unbox_usize(v_stop_821_);
    lean_dec(v_stop_821_);
    v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_boxed_827_, v_as_819_, v_i_boxed_828_, v_stop_boxed_829_, v_b_822_, v___y_823_, v___y_824_, v___y_825_);
    lean_dec(v___y_825_);
    lean_dec_ref(v___y_824_);
    lean_dec(v___y_823_);
    lean_dec_ref(v_as_819_);
    return v_res_830_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go___boxed(
    mut v_names_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
    mut v_a_834_: *mut LeanObject,
    mut v_a_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_836_: *mut LeanObject = core::ptr::null_mut();
    v_res_836_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(
        v_names_831_,
        v_a_832_,
        v_a_833_,
        v_a_834_,
    );
    lean_dec(v_a_834_);
    lean_dec_ref(v_a_833_);
    lean_dec(v_a_832_);
    lean_dec_ref(v_names_831_);
    return v_res_836_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode___boxed(
    mut v_code_837_: *mut LeanObject,
    mut v_a_838_: *mut LeanObject,
    mut v_a_839_: *mut LeanObject,
    mut v_a_840_: *mut LeanObject,
    mut v_a_841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_842_: *mut LeanObject = core::ptr::null_mut();
    v_res_842_ =
        l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(
            v_code_837_,
            v_a_838_,
            v_a_839_,
            v_a_840_,
        );
    lean_dec(v_a_840_);
    lean_dec_ref(v_a_839_);
    lean_dec(v_a_838_);
    return v_res_842_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0___boxed(
    mut v_pu_843_: *mut LeanObject,
    mut v_c_844_: *mut LeanObject,
    mut v___y_845_: *mut LeanObject,
    mut v___y_846_: *mut LeanObject,
    mut v___y_847_: *mut LeanObject,
    mut v___y_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_849_: u8 = 0;
    let mut v_res_850_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_849_ = (lean_unbox(v_pu_843_) as u8);
    v_res_850_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_boxed_849_, v_c_844_, v___y_845_, v___y_846_, v___y_847_);
    lean_dec(v___y_847_);
    lean_dec_ref(v___y_846_);
    lean_dec(v___y_845_);
    return v_res_850_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___boxed(
    mut v_as_851_: *mut LeanObject,
    mut v_i_852_: *mut LeanObject,
    mut v_stop_853_: *mut LeanObject,
    mut v_b_854_: *mut LeanObject,
    mut v___y_855_: *mut LeanObject,
    mut v___y_856_: *mut LeanObject,
    mut v___y_857_: *mut LeanObject,
    mut v___y_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_859_: usize = 0;
    let mut v_stop_boxed_860_: usize = 0;
    let mut v_res_861_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_859_ = lean_unbox_usize(v_i_852_);
    lean_dec(v_i_852_);
    v_stop_boxed_860_ = lean_unbox_usize(v_stop_853_);
    lean_dec(v_stop_853_);
    v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_as_851_, v_i_boxed_859_, v_stop_boxed_860_, v_b_854_, v___y_855_, v___y_856_, v___y_857_);
    lean_dec(v___y_857_);
    lean_dec_ref(v___y_856_);
    lean_dec(v___y_855_);
    lean_dec_ref(v_as_851_);
    return v_res_861_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(
    mut v_pu_862_: u8,
    mut v_f_863_: *mut LeanObject,
    mut v_v_864_: *mut LeanObject,
    mut v___y_865_: *mut LeanObject,
    mut v___y_866_: *mut LeanObject,
    mut v___y_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_863_, v_v_864_, v___y_865_, v___y_866_, v___y_867_);
    return v___x_869_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___boxed(
    mut v_pu_870_: *mut LeanObject,
    mut v_f_871_: *mut LeanObject,
    mut v_v_872_: *mut LeanObject,
    mut v___y_873_: *mut LeanObject,
    mut v___y_874_: *mut LeanObject,
    mut v___y_875_: *mut LeanObject,
    mut v___y_876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_877_: u8 = 0;
    let mut v_res_878_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_877_ = (lean_unbox(v_pu_870_) as u8);
    v_res_878_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(v_pu_boxed_877_, v_f_871_, v_v_872_, v___y_873_, v___y_874_, v___y_875_);
    lean_dec(v___y_875_);
    lean_dec_ref(v___y_874_);
    lean_dec(v___y_873_);
    return v_res_878_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1() -> *mut LeanObject {
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    v___x_881_ = l_Lean_Compiler_LCNF_collectUsedDecls___closed__0;
    v___x_882_ = l_Lean_NameSet_empty;
    v___x_883_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_883_, 0, v___x_882_);
    lean_ctor_set(v___x_883_, 1, v___x_881_);
    lean_ctor_set(v___x_883_, 2, v___x_881_);
    return v___x_883_;
}
pub unsafe fn l_Lean_Compiler_LCNF_collectUsedDecls(
    mut v_decls_884_: *mut LeanObject,
    mut v_a_885_: *mut LeanObject,
    mut v_a_886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localDecls_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extSigs_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_unused_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_906_: u8 = 0;
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_888_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_collectUsedDecls___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_collectUsedDecls___closed__1_once),
                    _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1,
                );
                v___x_889_ = lean_st_mk_ref(v___x_888_);
                v___x_890_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v_decls_884_, v___x_889_, v_a_885_, v_a_886_);
                if lean_obj_tag(v___x_890_) == 0 {
                    v_isSharedCheck_901_ = (!lean_is_exclusive(v___x_890_)) as u8;
                    if v_isSharedCheck_901_ == 0 {
                        v_unused_902_ = lean_ctor_get(v___x_890_, 0);
                        lean_dec(v_unused_902_);
                        v___x_892_ = v___x_890_;
                        v_isShared_893_ = v_isSharedCheck_901_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_890_);
                        v___x_892_ = lean_box(0);
                        v_isShared_893_ = v_isSharedCheck_901_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_889_);
                    v_a_903_ = lean_ctor_get(v___x_890_, 0);
                    v_isSharedCheck_910_ = (!lean_is_exclusive(v___x_890_)) as u8;
                    if v_isSharedCheck_910_ == 0 {
                        v___x_905_ = v___x_890_;
                        v_isShared_906_ = v_isSharedCheck_910_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_903_);
                        lean_dec(v___x_890_);
                        v___x_905_ = lean_box(0);
                        v_isShared_906_ = v_isSharedCheck_910_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_894_ = lean_st_ref_get(v___x_889_);
                lean_dec(v___x_889_);
                v_localDecls_895_ = lean_ctor_get(v___x_894_, 1);
                lean_inc_ref(v_localDecls_895_);
                v_extSigs_896_ = lean_ctor_get(v___x_894_, 2);
                lean_inc_ref(v_extSigs_896_);
                lean_dec(v___x_894_);
                v___x_897_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_897_, 0, v_localDecls_895_);
                lean_ctor_set(v___x_897_, 1, v_extSigs_896_);
                if v_isShared_893_ == 0 {
                    lean_ctor_set(v___x_892_, 0, v___x_897_);
                    v___x_899_ = v___x_892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
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
                    v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
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
    mut v_decls_911_: *mut LeanObject,
    mut v_a_912_: *mut LeanObject,
    mut v_a_913_: *mut LeanObject,
    mut v_a_914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_915_: *mut LeanObject = core::ptr::null_mut();
    v_res_915_ = l_Lean_Compiler_LCNF_collectUsedDecls(v_decls_911_, v_a_912_, v_a_913_);
    lean_dec(v_a_913_);
    lean_dec_ref(v_a_912_);
    lean_dec_ref(v_decls_911_);
    return v_res_915_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(
    mut v_modulePrefix_916_: *mut LeanObject,
    mut v_as_917_: *mut LeanObject,
    mut v_i_918_: usize,
    mut v_stop_919_: usize,
) -> u8 {
    let mut v___x_920_: u8 = 0;
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_irPhases_923_: u8 = 0;
    let mut v___x_924_: u8 = 0;
    let mut v___y_926_: u8 = 0;
    let mut v___x_927_: usize = 0;
    let mut v___x_928_: usize = 0;
    let mut v___x_930_: u8 = 0;
    let mut v___x_931_: u8 = 0;
    let mut v_module_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: u8 = 0;
    let mut v___x_934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_920_ = lean_usize_dec_eq(v_i_918_, v_stop_919_);
                if v___x_920_ == 0 {
                    v___x_921_ = lean_array_uget_borrowed(v_as_917_, v_i_918_);
                    v_toImport_922_ = lean_ctor_get(v___x_921_, 0);
                    v_irPhases_923_ = lean_ctor_get_uint8(
                        v___x_921_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v___x_924_ = 1;
                    v___x_930_ = 1;
                    v___x_931_ = l_Lean_instBEqIRPhases_beq(v_irPhases_923_, v___x_930_);
                    if v___x_931_ == 0 {
                        v_module_932_ = lean_ctor_get(v_toImport_922_, 0);
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
    mut v_modulePrefix_935_: *mut LeanObject,
    mut v_as_936_: *mut LeanObject,
    mut v_i_937_: *mut LeanObject,
    mut v_stop_938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_939_: usize = 0;
    let mut v_stop_boxed_940_: usize = 0;
    let mut v_res_941_: u8 = 0;
    let mut v_r_942_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_939_ = lean_unbox_usize(v_i_937_);
    lean_dec(v_i_937_);
    v_stop_boxed_940_ = lean_unbox_usize(v_stop_938_);
    lean_dec(v_stop_938_);
    v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_935_, v_as_936_, v_i_boxed_939_, v_stop_boxed_940_);
    lean_dec_ref(v_as_936_);
    lean_dec(v_modulePrefix_935_);
    v_r_942_ = lean_box((v_res_941_) as usize);
    return v_r_942_;
}
pub unsafe fn l_Lean_Compiler_LCNF_usesModuleFrom(
    mut v_env_943_: *mut LeanObject,
    mut v_modulePrefix_944_: *mut LeanObject,
) -> u8 {
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: u8 = 0;
    v___x_945_ = l_Lean_Environment_header(v_env_943_);
    v_modules_946_ = lean_ctor_get(v___x_945_, 3);
    lean_inc_ref(v_modules_946_);
    lean_dec_ref(v___x_945_);
    v___x_947_ = lean_unsigned_to_nat(0);
    v___x_948_ = lean_array_get_size(v_modules_946_);
    v___x_949_ = lean_nat_dec_lt(v___x_947_, v___x_948_);
    if v___x_949_ == 0 {
        lean_dec_ref(v_modules_946_);
        return v___x_949_;
    } else {
        if v___x_949_ == 0 {
            lean_dec_ref(v_modules_946_);
            return v___x_949_;
        } else {
            let mut v___x_950_: usize = 0;
            let mut v___x_951_: usize = 0;
            let mut v___x_952_: u8 = 0;
            v___x_950_ = 0usize;
            v___x_951_ = lean_usize_of_nat(v___x_948_);
            v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_944_, v_modules_946_, v___x_950_, v___x_951_);
            lean_dec_ref(v_modules_946_);
            return v___x_952_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_usesModuleFrom___boxed(
    mut v_env_953_: *mut LeanObject,
    mut v_modulePrefix_954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_955_: u8 = 0;
    let mut v_r_956_: *mut LeanObject = core::ptr::null_mut();
    v_res_955_ = l_Lean_Compiler_LCNF_usesModuleFrom(v_env_953_, v_modulePrefix_954_);
    lean_dec(v_modulePrefix_954_);
    lean_dec_ref(v_env_953_);
    v_r_956_ = lean_box((v_res_955_) as usize);
    return v_r_956_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_EmitUtil(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_EmitUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_EmitUtil(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_EmitUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_EmitUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_EmitUtil(builtin);
}
