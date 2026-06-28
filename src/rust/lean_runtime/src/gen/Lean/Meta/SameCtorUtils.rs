// Lean compiler output
// Module: Lean.Meta.SameCtorUtils
// Imports: Lean.Meta.Basic Lean.Meta.Transform
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Meta::Defs::lean_name_append_after;
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
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_findAsync_x3f,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop, l_Lean_Expr_bindingDomain_x21,
    l_Lean_Expr_bindingName_x21, l_Lean_Expr_constName_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_isForall, l_Lean_Expr_sort___override, l_Lean_mkAppN,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_type, lean_local_ctx_find};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofConstName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_whnfForall,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, l_Lean_Core_betaReduce, runtime_initialize_Lean_Meta_Transform,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::Util::FindExpr::l_Lean_Expr_occurs;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::lean_imports_rs::Lean::Util::FindExpr::lean_find_expr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_apply_7, lean_apply_9, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value) as *mut LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value
) as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value
) as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value
) as *mut LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value
) as *mut LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value
) as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_occursInCtorTypeMask___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_occursInCtorTypeMask___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_occursInCtorTypeMask___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 116, 46, 105, 115, 70, 111, 114, 97, 108, 108, 10, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value: LeanStringObject<70> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 97, 109, 101, 67, 116, 111, 114, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 119, 105, 116, 104, 83, 104, 97, 114, 101, 100, 67, 116, 111, 114, 73, 110, 100, 105, 99, 101, 115, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 97, 109, 101, 67, 116, 111, 114, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value: LeanArrayObject<
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
static mut l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(
    mut v_lctx_968_: *mut LeanObject,
    mut v_e_969_: *mut LeanObject,
    mut v_s_970_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_s_970_) == 1 {
        let mut v_fvarId_971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_971_ = lean_ctor_get(v_s_970_, 0);
        lean_inc(v_fvarId_971_);
        v___x_972_ = lean_local_ctx_find(v_lctx_968_, v_fvarId_971_);
        if lean_obj_tag(v___x_972_) == 1 {
            let mut v_val_973_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_974_: u8 = 0;
            v_val_973_ = lean_ctor_get(v___x_972_, 0);
            lean_inc(v_val_973_);
            lean_dec_ref_known(v___x_972_, 1);
            v___x_974_ = lean_expr_eqv(v_s_970_, v_e_969_);
            lean_dec_ref_known(v_s_970_, 1);
            if v___x_974_ == 0 {
                let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_976_: u8 = 0;
                v___x_975_ = l_Lean_LocalDecl_type(v_val_973_);
                lean_dec(v_val_973_);
                v___x_976_ = l_Lean_Expr_occurs(v_e_969_, v___x_975_);
                lean_dec_ref(v___x_975_);
                return v___x_976_;
            } else {
                lean_dec(v_val_973_);
                lean_dec_ref(v_e_969_);
                return v___x_974_;
            }
        } else {
            let mut v___x_977_: u8 = 0;
            lean_dec(v___x_972_);
            v___x_977_ = lean_expr_eqv(v_s_970_, v_e_969_);
            lean_dec_ref(v_e_969_);
            lean_dec_ref_known(v_s_970_, 1);
            return v___x_977_;
        }
    } else {
        let mut v___x_978_: u8 = 0;
        lean_dec_ref(v_lctx_968_);
        v___x_978_ = lean_expr_eqv(v_s_970_, v_e_969_);
        lean_dec_ref(v_e_969_);
        lean_dec_ref(v_s_970_);
        return v___x_978_;
    }
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed(
    mut v_lctx_979_: *mut LeanObject,
    mut v_e_980_: *mut LeanObject,
    mut v_s_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: u8 = 0;
    let mut v_r_983_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(
        v_lctx_979_,
        v_e_980_,
        v_s_981_,
    );
    v_r_983_ = lean_box((v_res_982_) as usize);
    return v_r_983_;
}
pub unsafe fn l_Lean_Meta_occursOrInType(
    mut v_lctx_984_: *mut LeanObject,
    mut v_e_985_: *mut LeanObject,
    mut v_t_986_: *mut LeanObject,
) -> u8 {
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    v___x_987_ = lean_alloc_closure(
        l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_987_, 0, v_lctx_984_);
    lean_closure_set(v___x_987_, 1, v_e_985_);
    v___x_988_ = lean_find_expr(v___x_987_, v_t_986_);
    lean_dec_ref(v___x_987_);
    if lean_obj_tag(v___x_988_) == 0 {
        let mut v___x_989_: u8 = 0;
        v___x_989_ = 0;
        return v___x_989_;
    } else {
        let mut v___x_990_: u8 = 0;
        lean_dec_ref_known(v___x_988_, 1);
        v___x_990_ = 1;
        return v___x_990_;
    }
}
pub unsafe fn l_Lean_Meta_occursOrInType___boxed(
    mut v_lctx_991_: *mut LeanObject,
    mut v_e_992_: *mut LeanObject,
    mut v_t_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_994_: u8 = 0;
    let mut v_r_995_: *mut LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Lean_Meta_occursOrInType(v_lctx_991_, v_e_992_, v_t_993_);
    lean_dec_ref(v_t_993_);
    v_r_995_ = lean_box((v_res_994_) as usize);
    return v_r_995_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(
    mut v_k_996_: *mut LeanObject,
    mut v_b_997_: *mut LeanObject,
    mut v_c_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
    mut v___y_1001_: *mut LeanObject,
    mut v___y_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1002_);
    lean_inc_ref(v___y_1001_);
    lean_inc(v___y_1000_);
    lean_inc_ref(v___y_999_);
    v___x_1004_ = lean_apply_7(
        v_k_996_,
        v_b_997_,
        v_c_998_,
        v___y_999_,
        v___y_1000_,
        v___y_1001_,
        v___y_1002_,
        lean_box(0),
    );
    return v___x_1004_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed(
    mut v_k_1005_: *mut LeanObject,
    mut v_b_1006_: *mut LeanObject,
    mut v_c_1007_: *mut LeanObject,
    mut v___y_1008_: *mut LeanObject,
    mut v___y_1009_: *mut LeanObject,
    mut v___y_1010_: *mut LeanObject,
    mut v___y_1011_: *mut LeanObject,
    mut v___y_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(v_k_1005_, v_b_1006_, v_c_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
    lean_dec(v___y_1011_);
    lean_dec_ref(v___y_1010_);
    lean_dec(v___y_1009_);
    lean_dec_ref(v___y_1008_);
    return v_res_1013_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(
    mut v_type_1014_: *mut LeanObject,
    mut v_maxFVars_x3f_1015_: *mut LeanObject,
    mut v_k_1016_: *mut LeanObject,
    mut v_cleanupAnnotations_1017_: u8,
    mut v_whnfType_1018_: u8,
    mut v___y_1019_: *mut LeanObject,
    mut v___y_1020_: *mut LeanObject,
    mut v___y_1021_: *mut LeanObject,
    mut v___y_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1033_: u8 = 0;
    let mut v_a_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1024_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_1024_, 0, v_k_1016_);
                v___x_1025_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_1014_,
                    v_maxFVars_x3f_1015_,
                    v___f_1024_,
                    v_cleanupAnnotations_1017_,
                    v_whnfType_1018_,
                    v___y_1019_,
                    v___y_1020_,
                    v___y_1021_,
                    v___y_1022_,
                );
                if lean_obj_tag(v___x_1025_) == 0 {
                    v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
                    v_isSharedCheck_1033_ = (!lean_is_exclusive(v___x_1025_)) as u8;
                    if v_isSharedCheck_1033_ == 0 {
                        v___x_1028_ = v___x_1025_;
                        v_isShared_1029_ = v_isSharedCheck_1033_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1026_);
                        lean_dec(v___x_1025_);
                        v___x_1028_ = lean_box(0);
                        v_isShared_1029_ = v_isSharedCheck_1033_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1034_ = lean_ctor_get(v___x_1025_, 0);
                    v_isSharedCheck_1041_ = (!lean_is_exclusive(v___x_1025_)) as u8;
                    if v_isSharedCheck_1041_ == 0 {
                        v___x_1036_ = v___x_1025_;
                        v_isShared_1037_ = v_isSharedCheck_1041_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1034_);
                        lean_dec(v___x_1025_);
                        v___x_1036_ = lean_box(0);
                        v_isShared_1037_ = v_isSharedCheck_1041_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1029_ == 0 {
                    v___x_1031_ = v___x_1028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
                    v___x_1031_ = v_reuseFailAlloc_1032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1031_;
            }
            3 => {
                if v_isShared_1037_ == 0 {
                    v___x_1039_ = v___x_1036_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
                    v___x_1039_ = v_reuseFailAlloc_1040_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___boxed(
    mut v_type_1042_: *mut LeanObject,
    mut v_maxFVars_x3f_1043_: *mut LeanObject,
    mut v_k_1044_: *mut LeanObject,
    mut v_cleanupAnnotations_1045_: *mut LeanObject,
    mut v_whnfType_1046_: *mut LeanObject,
    mut v___y_1047_: *mut LeanObject,
    mut v___y_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
    mut v___y_1050_: *mut LeanObject,
    mut v___y_1051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1052_: u8 = 0;
    let mut v_whnfType_boxed_1053_: u8 = 0;
    let mut v_res_1054_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1052_ = (lean_unbox(v_cleanupAnnotations_1045_) as u8);
    v_whnfType_boxed_1053_ = (lean_unbox(v_whnfType_1046_) as u8);
    v_res_1054_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(
            v_type_1042_,
            v_maxFVars_x3f_1043_,
            v_k_1044_,
            v_cleanupAnnotations_boxed_1052_,
            v_whnfType_boxed_1053_,
            v___y_1047_,
            v___y_1048_,
            v___y_1049_,
            v___y_1050_,
        );
    lean_dec(v___y_1050_);
    lean_dec_ref(v___y_1049_);
    lean_dec(v___y_1048_);
    lean_dec_ref(v___y_1047_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(
    mut v_00_u03b1_1055_: *mut LeanObject,
    mut v_type_1056_: *mut LeanObject,
    mut v_maxFVars_x3f_1057_: *mut LeanObject,
    mut v_k_1058_: *mut LeanObject,
    mut v_cleanupAnnotations_1059_: u8,
    mut v_whnfType_1060_: u8,
    mut v___y_1061_: *mut LeanObject,
    mut v___y_1062_: *mut LeanObject,
    mut v___y_1063_: *mut LeanObject,
    mut v___y_1064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    v___x_1066_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(
            v_type_1056_,
            v_maxFVars_x3f_1057_,
            v_k_1058_,
            v_cleanupAnnotations_1059_,
            v_whnfType_1060_,
            v___y_1061_,
            v___y_1062_,
            v___y_1063_,
            v___y_1064_,
        );
    return v___x_1066_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___boxed(
    mut v_00_u03b1_1067_: *mut LeanObject,
    mut v_type_1068_: *mut LeanObject,
    mut v_maxFVars_x3f_1069_: *mut LeanObject,
    mut v_k_1070_: *mut LeanObject,
    mut v_cleanupAnnotations_1071_: *mut LeanObject,
    mut v_whnfType_1072_: *mut LeanObject,
    mut v___y_1073_: *mut LeanObject,
    mut v___y_1074_: *mut LeanObject,
    mut v___y_1075_: *mut LeanObject,
    mut v___y_1076_: *mut LeanObject,
    mut v___y_1077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1078_: u8 = 0;
    let mut v_whnfType_boxed_1079_: u8 = 0;
    let mut v_res_1080_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1078_ = (lean_unbox(v_cleanupAnnotations_1071_) as u8);
    v_whnfType_boxed_1079_ = (lean_unbox(v_whnfType_1072_) as u8);
    v_res_1080_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(
            v_00_u03b1_1067_,
            v_type_1068_,
            v_maxFVars_x3f_1069_,
            v_k_1070_,
            v_cleanupAnnotations_boxed_1078_,
            v_whnfType_boxed_1079_,
            v___y_1073_,
            v___y_1074_,
            v___y_1075_,
            v___y_1076_,
        );
    lean_dec(v___y_1076_);
    lean_dec_ref(v___y_1075_);
    lean_dec(v___y_1074_);
    lean_dec_ref(v___y_1073_);
    return v_res_1080_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(
    mut v___x_1081_: *mut LeanObject,
    mut v_a_1082_: *mut LeanObject,
    mut v_sz_1083_: usize,
    mut v_i_1084_: usize,
    mut v_bs_1085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1086_: u8 = 0;
    let mut v_v_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1091_: usize = 0;
    let mut v___x_1092_: usize = 0;
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1086_ = lean_usize_dec_lt(v_i_1084_, v_sz_1083_);
                if v___x_1086_ == 0 {
                    lean_dec_ref(v___x_1081_);
                    return v_bs_1085_;
                } else {
                    v_v_1087_ = lean_array_uget(v_bs_1085_, v_i_1084_);
                    v___x_1088_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1089_ = lean_array_uset(v_bs_1085_, v_i_1084_, v___x_1088_);
                    lean_inc_ref(v___x_1081_);
                    v___x_1090_ = l_Lean_Meta_occursOrInType(v___x_1081_, v_v_1087_, v_a_1082_);
                    v___x_1091_ = 1usize;
                    v___x_1092_ = lean_usize_add(v_i_1084_, v___x_1091_);
                    v___x_1093_ = lean_box((v___x_1090_) as usize);
                    v___x_1094_ = lean_array_uset(v_bs_x27_1089_, v_i_1084_, v___x_1093_);
                    v_i_1084_ = v___x_1092_;
                    v_bs_1085_ = v___x_1094_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0___boxed(
    mut v___x_1096_: *mut LeanObject,
    mut v_a_1097_: *mut LeanObject,
    mut v_sz_1098_: *mut LeanObject,
    mut v_i_1099_: *mut LeanObject,
    mut v_bs_1100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1101_: usize = 0;
    let mut v_i_boxed_1102_: usize = 0;
    let mut v_res_1103_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1101_ = lean_unbox_usize(v_sz_1098_);
    lean_dec(v_sz_1098_);
    v_i_boxed_1102_ = lean_unbox_usize(v_i_1099_);
    lean_dec(v_i_1099_);
    v_res_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v___x_1096_, v_a_1097_, v_sz_boxed_1101_, v_i_boxed_1102_, v_bs_1100_);
    lean_dec_ref(v_a_1097_);
    return v_res_1103_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask___lam__0(
    mut v_ys_1104_: *mut LeanObject,
    mut v_ctorRet_1105_: *mut LeanObject,
    mut v___y_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
    mut v___y_1109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v_lctx_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1119_: usize = 0;
    let mut v___x_1120_: usize = 0;
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut v_a_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1129_: u8 = 0;
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1133_: u8 = 0;
    let mut v_a_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1137_: u8 = 0;
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1109_);
                lean_inc_ref(v___y_1108_);
                lean_inc(v___y_1107_);
                lean_inc_ref(v___y_1106_);
                v___x_1111_ = lean_whnf(
                    v_ctorRet_1105_,
                    v___y_1106_,
                    v___y_1107_,
                    v___y_1108_,
                    v___y_1109_,
                );
                if lean_obj_tag(v___x_1111_) == 0 {
                    v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
                    lean_inc(v_a_1112_);
                    lean_dec_ref_known(v___x_1111_, 1);
                    v___x_1113_ = l_Lean_Core_betaReduce(v_a_1112_, v___y_1108_, v___y_1109_);
                    if lean_obj_tag(v___x_1113_) == 0 {
                        v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
                        v_isSharedCheck_1125_ = (!lean_is_exclusive(v___x_1113_)) as u8;
                        if v_isSharedCheck_1125_ == 0 {
                            v___x_1116_ = v___x_1113_;
                            v_isShared_1117_ = v_isSharedCheck_1125_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1114_);
                            lean_dec(v___x_1113_);
                            v___x_1116_ = lean_box(0);
                            v_isShared_1117_ = v_isSharedCheck_1125_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_ys_1104_);
                        v_a_1126_ = lean_ctor_get(v___x_1113_, 0);
                        v_isSharedCheck_1133_ = (!lean_is_exclusive(v___x_1113_)) as u8;
                        if v_isSharedCheck_1133_ == 0 {
                            v___x_1128_ = v___x_1113_;
                            v_isShared_1129_ = v_isSharedCheck_1133_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1126_);
                            lean_dec(v___x_1113_);
                            v___x_1128_ = lean_box(0);
                            v_isShared_1129_ = v_isSharedCheck_1133_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_ys_1104_);
                    v_a_1134_ = lean_ctor_get(v___x_1111_, 0);
                    v_isSharedCheck_1141_ = (!lean_is_exclusive(v___x_1111_)) as u8;
                    if v_isSharedCheck_1141_ == 0 {
                        v___x_1136_ = v___x_1111_;
                        v_isShared_1137_ = v_isSharedCheck_1141_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1134_);
                        lean_dec(v___x_1111_);
                        v___x_1136_ = lean_box(0);
                        v_isShared_1137_ = v_isSharedCheck_1141_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_lctx_1118_ = lean_ctor_get(v___y_1106_, 2);
                v_sz_1119_ = lean_array_size(v_ys_1104_);
                v___x_1120_ = 0usize;
                lean_inc_ref(v_lctx_1118_);
                v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v_lctx_1118_, v_a_1114_, v_sz_1119_, v___x_1120_, v_ys_1104_);
                lean_dec(v_a_1114_);
                if v_isShared_1117_ == 0 {
                    lean_ctor_set(v___x_1116_, 0, v___x_1121_);
                    v___x_1123_ = v___x_1116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
                    v___x_1123_ = v_reuseFailAlloc_1124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1123_;
            }
            3 => {
                if v_isShared_1129_ == 0 {
                    v___x_1131_ = v___x_1128_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
                    v___x_1131_ = v_reuseFailAlloc_1132_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1131_;
            }
            5 => {
                if v_isShared_1137_ == 0 {
                    v___x_1139_ = v___x_1136_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
                    v___x_1139_ = v_reuseFailAlloc_1140_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed(
    mut v_ys_1142_: *mut LeanObject,
    mut v_ctorRet_1143_: *mut LeanObject,
    mut v___y_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
    mut v___y_1148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1149_: *mut LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Lean_Meta_occursInCtorTypeMask___lam__0(
        v_ys_1142_,
        v_ctorRet_1143_,
        v___y_1144_,
        v___y_1145_,
        v___y_1146_,
        v___y_1147_,
    );
    lean_dec(v___y_1147_);
    lean_dec_ref(v___y_1146_);
    lean_dec(v___y_1145_);
    lean_dec_ref(v___y_1144_);
    return v_res_1149_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask___lam__1(
    mut v_numFields_1150_: *mut LeanObject,
    mut v___f_1151_: *mut LeanObject,
    mut v_x_1152_: *mut LeanObject,
    mut v_ctorRet_1153_: *mut LeanObject,
    mut v___y_1154_: *mut LeanObject,
    mut v___y_1155_: *mut LeanObject,
    mut v___y_1156_: *mut LeanObject,
    mut v___y_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1159_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1159_, 0, v_numFields_1150_);
    v___x_1160_ = 0;
    v___x_1161_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(
            v_ctorRet_1153_,
            v___x_1159_,
            v___f_1151_,
            v___x_1160_,
            v___x_1160_,
            v___y_1154_,
            v___y_1155_,
            v___y_1156_,
            v___y_1157_,
        );
    return v___x_1161_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed(
    mut v_numFields_1162_: *mut LeanObject,
    mut v___f_1163_: *mut LeanObject,
    mut v_x_1164_: *mut LeanObject,
    mut v_ctorRet_1165_: *mut LeanObject,
    mut v___y_1166_: *mut LeanObject,
    mut v___y_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
    mut v___y_1169_: *mut LeanObject,
    mut v___y_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1171_: *mut LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Lean_Meta_occursInCtorTypeMask___lam__1(
        v_numFields_1162_,
        v___f_1163_,
        v_x_1164_,
        v_ctorRet_1165_,
        v___y_1166_,
        v___y_1167_,
        v___y_1168_,
        v___y_1169_,
    );
    lean_dec(v___y_1169_);
    lean_dec_ref(v___y_1168_);
    lean_dec(v___y_1167_);
    lean_dec_ref(v___y_1166_);
    lean_dec_ref(v_x_1164_);
    return v_res_1171_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_instMonadEIO(lean_box(0));
    return v___x_1172_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(
    mut v_msg_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
    mut v___y_1179_: *mut LeanObject,
    mut v___y_1180_: *mut LeanObject,
    mut v___y_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1188_: u8 = 0;
    let mut v_toFunctor_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1195_: u8 = 0;
    let mut v___f_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1212_: u8 = 0;
    let mut v_toFunctor_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1219_: u8 = 0;
    let mut v___f_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065__overap_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut v_unused_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_unused_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v_unused_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1246_: u8 = 0;
    let mut v_unused_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1183_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0);
                v___x_1184_ = l_StateRefT_x27_instMonad___redArg(v___x_1183_);
                v_toApplicative_1185_ = lean_ctor_get(v___x_1184_, 0);
                v_isSharedCheck_1246_ = (!lean_is_exclusive(v___x_1184_)) as u8;
                if v_isSharedCheck_1246_ == 0 {
                    v_unused_1247_ = lean_ctor_get(v___x_1184_, 1);
                    lean_dec(v_unused_1247_);
                    v___x_1187_ = v___x_1184_;
                    v_isShared_1188_ = v_isSharedCheck_1246_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1185_);
                    lean_dec(v___x_1184_);
                    v___x_1187_ = lean_box(0);
                    v_isShared_1188_ = v_isSharedCheck_1246_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1189_ = lean_ctor_get(v_toApplicative_1185_, 0);
                v_toSeq_1190_ = lean_ctor_get(v_toApplicative_1185_, 2);
                v_toSeqLeft_1191_ = lean_ctor_get(v_toApplicative_1185_, 3);
                v_toSeqRight_1192_ = lean_ctor_get(v_toApplicative_1185_, 4);
                v_isSharedCheck_1244_ = (!lean_is_exclusive(v_toApplicative_1185_)) as u8;
                if v_isSharedCheck_1244_ == 0 {
                    v_unused_1245_ = lean_ctor_get(v_toApplicative_1185_, 1);
                    lean_dec(v_unused_1245_);
                    v___x_1194_ = v_toApplicative_1185_;
                    v_isShared_1195_ = v_isSharedCheck_1244_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1192_);
                    lean_inc(v_toSeqLeft_1191_);
                    lean_inc(v_toSeq_1190_);
                    lean_inc(v_toFunctor_1189_);
                    lean_dec(v_toApplicative_1185_);
                    v___x_1194_ = lean_box(0);
                    v_isShared_1195_ = v_isSharedCheck_1244_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1196_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1;
                v___f_1197_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2;
                lean_inc_ref(v_toFunctor_1189_);
                v___f_1198_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1198_, 0, v_toFunctor_1189_);
                v___f_1199_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1199_, 0, v_toFunctor_1189_);
                v___x_1200_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1200_, 0, v___f_1198_);
                lean_ctor_set(v___x_1200_, 1, v___f_1199_);
                v___f_1201_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1201_, 0, v_toSeqRight_1192_);
                v___f_1202_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1202_, 0, v_toSeqLeft_1191_);
                v___f_1203_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1203_, 0, v_toSeq_1190_);
                if v_isShared_1195_ == 0 {
                    lean_ctor_set(v___x_1194_, 4, v___f_1201_);
                    lean_ctor_set(v___x_1194_, 3, v___f_1202_);
                    lean_ctor_set(v___x_1194_, 2, v___f_1203_);
                    lean_ctor_set(v___x_1194_, 1, v___f_1196_);
                    lean_ctor_set(v___x_1194_, 0, v___x_1200_);
                    v___x_1205_ = v___x_1194_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1200_);
                    lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___f_1196_);
                    lean_ctor_set(v_reuseFailAlloc_1243_, 2, v___f_1203_);
                    lean_ctor_set(v_reuseFailAlloc_1243_, 3, v___f_1202_);
                    lean_ctor_set(v_reuseFailAlloc_1243_, 4, v___f_1201_);
                    v___x_1205_ = v_reuseFailAlloc_1243_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1188_ == 0 {
                    lean_ctor_set(v___x_1187_, 1, v___f_1197_);
                    lean_ctor_set(v___x_1187_, 0, v___x_1205_);
                    v___x_1207_ = v___x_1187_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1205_);
                    lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___f_1197_);
                    v___x_1207_ = v_reuseFailAlloc_1242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1208_ = l_StateRefT_x27_instMonad___redArg(v___x_1207_);
                v_toApplicative_1209_ = lean_ctor_get(v___x_1208_, 0);
                v_isSharedCheck_1240_ = (!lean_is_exclusive(v___x_1208_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v_unused_1241_ = lean_ctor_get(v___x_1208_, 1);
                    lean_dec(v_unused_1241_);
                    v___x_1211_ = v___x_1208_;
                    v_isShared_1212_ = v_isSharedCheck_1240_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1209_);
                    lean_dec(v___x_1208_);
                    v___x_1211_ = lean_box(0);
                    v_isShared_1212_ = v_isSharedCheck_1240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1213_ = lean_ctor_get(v_toApplicative_1209_, 0);
                v_toSeq_1214_ = lean_ctor_get(v_toApplicative_1209_, 2);
                v_toSeqLeft_1215_ = lean_ctor_get(v_toApplicative_1209_, 3);
                v_toSeqRight_1216_ = lean_ctor_get(v_toApplicative_1209_, 4);
                v_isSharedCheck_1238_ = (!lean_is_exclusive(v_toApplicative_1209_)) as u8;
                if v_isSharedCheck_1238_ == 0 {
                    v_unused_1239_ = lean_ctor_get(v_toApplicative_1209_, 1);
                    lean_dec(v_unused_1239_);
                    v___x_1218_ = v_toApplicative_1209_;
                    v_isShared_1219_ = v_isSharedCheck_1238_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1216_);
                    lean_inc(v_toSeqLeft_1215_);
                    lean_inc(v_toSeq_1214_);
                    lean_inc(v_toFunctor_1213_);
                    lean_dec(v_toApplicative_1209_);
                    v___x_1218_ = lean_box(0);
                    v_isShared_1219_ = v_isSharedCheck_1238_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1220_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3;
                v___f_1221_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4;
                lean_inc_ref(v_toFunctor_1213_);
                v___f_1222_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1222_, 0, v_toFunctor_1213_);
                v___f_1223_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1223_, 0, v_toFunctor_1213_);
                v___x_1224_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1224_, 0, v___f_1222_);
                lean_ctor_set(v___x_1224_, 1, v___f_1223_);
                v___f_1225_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1225_, 0, v_toSeqRight_1216_);
                v___f_1226_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1226_, 0, v_toSeqLeft_1215_);
                v___f_1227_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1227_, 0, v_toSeq_1214_);
                if v_isShared_1219_ == 0 {
                    lean_ctor_set(v___x_1218_, 4, v___f_1225_);
                    lean_ctor_set(v___x_1218_, 3, v___f_1226_);
                    lean_ctor_set(v___x_1218_, 2, v___f_1227_);
                    lean_ctor_set(v___x_1218_, 1, v___f_1220_);
                    lean_ctor_set(v___x_1218_, 0, v___x_1224_);
                    v___x_1229_ = v___x_1218_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1224_);
                    lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___f_1220_);
                    lean_ctor_set(v_reuseFailAlloc_1237_, 2, v___f_1227_);
                    lean_ctor_set(v_reuseFailAlloc_1237_, 3, v___f_1226_);
                    lean_ctor_set(v_reuseFailAlloc_1237_, 4, v___f_1225_);
                    v___x_1229_ = v_reuseFailAlloc_1237_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1212_ == 0 {
                    lean_ctor_set(v___x_1211_, 1, v___f_1221_);
                    lean_ctor_set(v___x_1211_, 0, v___x_1229_);
                    v___x_1231_ = v___x_1211_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1229_);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___f_1221_);
                    v___x_1231_ = v_reuseFailAlloc_1236_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1232_ = lean_box(0);
                v___x_1233_ = l_instInhabitedOfMonad___redArg(v___x_1231_, v___x_1232_);
                v___x_2065__overap_1234_ = lean_panic_fn_borrowed(v___x_1233_, v_msg_1177_);
                lean_dec(v___x_1233_);
                lean_inc(v___y_1181_);
                lean_inc_ref(v___y_1180_);
                lean_inc(v___y_1179_);
                lean_inc_ref(v___y_1178_);
                v___x_1235_ = lean_apply_5(
                    v___x_2065__overap_1234_,
                    v___y_1178_,
                    v___y_1179_,
                    v___y_1180_,
                    v___y_1181_,
                    lean_box(0),
                );
                return v___x_1235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___boxed(
    mut v_msg_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1254_: *mut LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v_msg_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
    lean_dec(v___y_1252_);
    lean_dec_ref(v___y_1251_);
    lean_dec(v___y_1250_);
    lean_dec_ref(v___y_1249_);
    return v_res_1254_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(
    mut v_msgData_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
    mut v___y_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ = lean_st_ref_get(v___y_1259_);
    v_env_1262_ = lean_ctor_get(v___x_1261_, 0);
    lean_inc_ref(v_env_1262_);
    lean_dec(v___x_1261_);
    v___x_1263_ = lean_st_ref_get(v___y_1257_);
    v_mctx_1264_ = lean_ctor_get(v___x_1263_, 0);
    lean_inc_ref(v_mctx_1264_);
    lean_dec(v___x_1263_);
    v_lctx_1265_ = lean_ctor_get(v___y_1256_, 2);
    v_options_1266_ = lean_ctor_get(v___y_1258_, 2);
    lean_inc_ref(v_options_1266_);
    lean_inc_ref(v_lctx_1265_);
    v___x_1267_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1267_, 0, v_env_1262_);
    lean_ctor_set(v___x_1267_, 1, v_mctx_1264_);
    lean_ctor_set(v___x_1267_, 2, v_lctx_1265_);
    lean_ctor_set(v___x_1267_, 3, v_options_1266_);
    v___x_1268_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    lean_ctor_set(v___x_1268_, 1, v_msgData_1255_);
    v___x_1269_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1269_, 0, v___x_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_1270_: *mut LeanObject,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1276_: *mut LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msgData_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
    lean_dec(v___y_1274_);
    lean_dec_ref(v___y_1273_);
    lean_dec(v___y_1272_);
    lean_dec_ref(v___y_1271_);
    return v_res_1276_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(
    mut v_msg_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1293_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1283_ = lean_ctor_get(v___y_1280_, 5);
                v___x_1284_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msg_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
                v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
                v_isSharedCheck_1293_ = (!lean_is_exclusive(v___x_1284_)) as u8;
                if v_isSharedCheck_1293_ == 0 {
                    v___x_1287_ = v___x_1284_;
                    v_isShared_1288_ = v_isSharedCheck_1293_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1285_);
                    lean_dec(v___x_1284_);
                    v___x_1287_ = lean_box(0);
                    v_isShared_1288_ = v_isSharedCheck_1293_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1283_);
                v___x_1289_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1289_, 0, v_ref_1283_);
                lean_ctor_set(v___x_1289_, 1, v_a_1285_);
                if v_isShared_1288_ == 0 {
                    lean_ctor_set_tag(v___x_1287_, 1);
                    lean_ctor_set(v___x_1287_, 0, v___x_1289_);
                    v___x_1291_ = v___x_1287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
                    v___x_1291_ = v_reuseFailAlloc_1292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1291_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg___boxed(
    mut v_msg_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1300_: *mut LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
    lean_dec(v___y_1298_);
    lean_dec_ref(v___y_1297_);
    lean_dec(v___y_1296_);
    lean_dec_ref(v___y_1295_);
    return v_res_1300_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0;
    v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    v___x_1305_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2;
    v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
    return v___x_1306_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7()
-> *mut LeanObject {
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    v___x_1310_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6;
    v___x_1311_ = lean_unsigned_to_nat(11);
    v___x_1312_ = lean_unsigned_to_nat(122);
    v___x_1313_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5;
    v___x_1314_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4;
    v___x_1315_ = l_mkPanicMessageWithDecl(
        v___x_1314_,
        v___x_1313_,
        v___x_1312_,
        v___x_1311_,
        v___x_1310_,
    );
    return v___x_1315_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(
    mut v_constName_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
    mut v___y_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: u8 = 0;
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1335_: u8 = 0;
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v_val_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_a_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1330_ = lean_st_ref_get(v___y_1320_);
                v_env_1331_ = lean_ctor_get(v___x_1330_, 0);
                lean_inc_ref(v_env_1331_);
                lean_dec(v___x_1330_);
                v___x_1332_ = 0;
                lean_inc(v_constName_1316_);
                v___x_1333_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1331_, v_constName_1316_, v___x_1332_);
                if lean_obj_tag(v___x_1333_) == 1 {
                    v_val_1334_ = lean_ctor_get(v___x_1333_, 0);
                    lean_inc(v_val_1334_);
                    lean_dec_ref_known(v___x_1333_, 1);
                    v_kind_1335_ = lean_ctor_get_uint8(
                        v_val_1334_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_kind_1335_ == 6 {
                        v___x_1336_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1334_);
                        if lean_obj_tag(v___x_1336_) == 6 {
                            lean_dec(v_constName_1316_);
                            v_val_1337_ = lean_ctor_get(v___x_1336_, 0);
                            v_isSharedCheck_1344_ = (!lean_is_exclusive(v___x_1336_)) as u8;
                            if v_isSharedCheck_1344_ == 0 {
                                v___x_1339_ = v___x_1336_;
                                v_isShared_1340_ = v_isSharedCheck_1344_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_1337_);
                                lean_dec(v___x_1336_);
                                v___x_1339_ = lean_box(0);
                                v_isShared_1340_ = v_isSharedCheck_1344_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_1336_);
                            v___x_1345_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7);
                            v___x_1346_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v___x_1345_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
                            if lean_obj_tag(v___x_1346_) == 0 {
                                v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
                                v_isSharedCheck_1355_ = (!lean_is_exclusive(v___x_1346_)) as u8;
                                if v_isSharedCheck_1355_ == 0 {
                                    v___x_1349_ = v___x_1346_;
                                    v_isShared_1350_ = v_isSharedCheck_1355_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_1347_);
                                    lean_dec(v___x_1346_);
                                    v___x_1349_ = lean_box(0);
                                    v_isShared_1350_ = v_isSharedCheck_1355_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_constName_1316_);
                                v_a_1356_ = lean_ctor_get(v___x_1346_, 0);
                                v_isSharedCheck_1363_ = (!lean_is_exclusive(v___x_1346_)) as u8;
                                if v_isSharedCheck_1363_ == 0 {
                                    v___x_1358_ = v___x_1346_;
                                    v_isShared_1359_ = v_isSharedCheck_1363_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_1356_);
                                    lean_dec(v___x_1346_);
                                    v___x_1358_ = lean_box(0);
                                    v_isShared_1359_ = v_isSharedCheck_1363_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_1334_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1333_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1323_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
                v___x_1324_ = 0;
                v___x_1325_ = l_Lean_MessageData_ofConstName(v_constName_1316_, v___x_1324_);
                v___x_1326_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1326_, 0, v___x_1323_);
                lean_ctor_set(v___x_1326_, 1, v___x_1325_);
                v___x_1327_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3);
                v___x_1328_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1328_, 0, v___x_1326_);
                lean_ctor_set(v___x_1328_, 1, v___x_1327_);
                v___x_1329_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_1328_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
                return v___x_1329_;
            }
            2 => {
                if v_isShared_1340_ == 0 {
                    lean_ctor_set_tag(v___x_1339_, 0);
                    v___x_1342_ = v___x_1339_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_val_1337_);
                    v___x_1342_ = v_reuseFailAlloc_1343_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1342_;
            }
            4 => {
                if lean_obj_tag(v_a_1347_) == 0 {
                    lean_del_object(v___x_1349_);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_constName_1316_);
                    v_val_1351_ = lean_ctor_get(v_a_1347_, 0);
                    lean_inc(v_val_1351_);
                    lean_dec_ref_known(v_a_1347_, 1);
                    if v_isShared_1350_ == 0 {
                        lean_ctor_set(v___x_1349_, 0, v_val_1351_);
                        v___x_1353_ = v___x_1349_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_val_1351_);
                        v___x_1353_ = v_reuseFailAlloc_1354_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1353_;
            }
            6 => {
                if v_isShared_1359_ == 0 {
                    v___x_1361_ = v___x_1358_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
                    v___x_1361_ = v_reuseFailAlloc_1362_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___boxed(
    mut v_constName_1364_: *mut LeanObject,
    mut v___y_1365_: *mut LeanObject,
    mut v___y_1366_: *mut LeanObject,
    mut v___y_1367_: *mut LeanObject,
    mut v___y_1368_: *mut LeanObject,
    mut v___y_1369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1370_: *mut LeanObject = core::ptr::null_mut();
    v_res_1370_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(
        v_constName_1364_,
        v___y_1365_,
        v___y_1366_,
        v___y_1367_,
        v___y_1368_,
    );
    lean_dec(v___y_1368_);
    lean_dec_ref(v___y_1367_);
    lean_dec(v___y_1366_);
    lean_dec_ref(v___y_1365_);
    return v_res_1370_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask(
    mut v_ctorName_1372_: *mut LeanObject,
    mut v_a_1373_: *mut LeanObject,
    mut v_a_1374_: *mut LeanObject,
    mut v_a_1375_: *mut LeanObject,
    mut v_a_1376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1392_: u8 = 0;
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1378_ =
                    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(
                        v_ctorName_1372_,
                        v_a_1373_,
                        v_a_1374_,
                        v_a_1375_,
                        v_a_1376_,
                    );
                if lean_obj_tag(v___x_1378_) == 0 {
                    v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
                    lean_inc(v_a_1379_);
                    lean_dec_ref_known(v___x_1378_, 1);
                    v_toConstantVal_1380_ = lean_ctor_get(v_a_1379_, 0);
                    lean_inc_ref(v_toConstantVal_1380_);
                    v_numParams_1381_ = lean_ctor_get(v_a_1379_, 3);
                    lean_inc(v_numParams_1381_);
                    v_numFields_1382_ = lean_ctor_get(v_a_1379_, 4);
                    lean_inc(v_numFields_1382_);
                    lean_dec(v_a_1379_);
                    v_type_1383_ = lean_ctor_get(v_toConstantVal_1380_, 2);
                    lean_inc_ref(v_type_1383_);
                    lean_dec_ref(v_toConstantVal_1380_);
                    v___f_1384_ = l_Lean_Meta_occursInCtorTypeMask___closed__0;
                    v___f_1385_ = lean_alloc_closure(
                        l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___f_1385_, 0, v_numFields_1382_);
                    lean_closure_set(v___f_1385_, 1, v___f_1384_);
                    v___x_1386_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1386_, 0, v_numParams_1381_);
                    v___x_1387_ = 0;
                    v___x_1388_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_1383_, v___x_1386_, v___f_1385_, v___x_1387_, v___x_1387_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
                    return v___x_1388_;
                } else {
                    v_a_1389_ = lean_ctor_get(v___x_1378_, 0);
                    v_isSharedCheck_1396_ = (!lean_is_exclusive(v___x_1378_)) as u8;
                    if v_isSharedCheck_1396_ == 0 {
                        v___x_1391_ = v___x_1378_;
                        v_isShared_1392_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1389_);
                        lean_dec(v___x_1378_);
                        v___x_1391_ = lean_box(0);
                        v_isShared_1392_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1392_ == 0 {
                    v___x_1394_ = v___x_1391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
                    v___x_1394_ = v_reuseFailAlloc_1395_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask___boxed(
    mut v_ctorName_1397_: *mut LeanObject,
    mut v_a_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
    mut v_a_1400_: *mut LeanObject,
    mut v_a_1401_: *mut LeanObject,
    mut v_a_1402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1403_: *mut LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lean_Meta_occursInCtorTypeMask(
        v_ctorName_1397_,
        v_a_1398_,
        v_a_1399_,
        v_a_1400_,
        v_a_1401_,
    );
    lean_dec(v_a_1401_);
    lean_dec_ref(v_a_1400_);
    lean_dec(v_a_1399_);
    lean_dec_ref(v_a_1398_);
    return v_res_1403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(
    mut v_00_u03b1_1404_: *mut LeanObject,
    mut v_msg_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    v___x_1411_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
    return v___x_1411_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___boxed(
    mut v_00_u03b1_1412_: *mut LeanObject,
    mut v_msg_1413_: *mut LeanObject,
    mut v___y_1414_: *mut LeanObject,
    mut v___y_1415_: *mut LeanObject,
    mut v___y_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1419_: *mut LeanObject = core::ptr::null_mut();
    v_res_1419_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(v_00_u03b1_1412_, v_msg_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
    lean_dec(v___y_1417_);
    lean_dec_ref(v___y_1416_);
    lean_dec(v___y_1415_);
    lean_dec_ref(v___y_1414_);
    return v_res_1419_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(
    mut v_msg_1421_: *mut LeanObject,
    mut v___y_1422_: *mut LeanObject,
    mut v___y_1423_: *mut LeanObject,
    mut v___y_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685__overap_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    v___f_1427_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0;
    v___x_685__overap_1428_ = lean_panic_fn_borrowed(v___f_1427_, v_msg_1421_);
    lean_inc(v___y_1425_);
    lean_inc_ref(v___y_1424_);
    lean_inc(v___y_1423_);
    lean_inc_ref(v___y_1422_);
    v___x_1429_ = lean_apply_5(
        v___x_685__overap_1428_,
        v___y_1422_,
        v___y_1423_,
        v___y_1424_,
        v___y_1425_,
        lean_box(0),
    );
    return v___x_1429_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___boxed(
    mut v_msg_1430_: *mut LeanObject,
    mut v___y_1431_: *mut LeanObject,
    mut v___y_1432_: *mut LeanObject,
    mut v___y_1433_: *mut LeanObject,
    mut v___y_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1436_: *mut LeanObject = core::ptr::null_mut();
    v_res_1436_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
    lean_dec(v___y_1434_);
    lean_dec_ref(v___y_1433_);
    lean_dec(v___y_1432_);
    lean_dec_ref(v___y_1431_);
    return v_res_1436_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(
    mut v_00_u03b1_1437_: *mut LeanObject,
    mut v_msg_1438_: *mut LeanObject,
    mut v___y_1439_: *mut LeanObject,
    mut v___y_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
    mut v___y_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1444_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
    return v___x_1444_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___boxed(
    mut v_00_u03b1_1445_: *mut LeanObject,
    mut v_msg_1446_: *mut LeanObject,
    mut v___y_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
    mut v___y_1449_: *mut LeanObject,
    mut v___y_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1452_: *mut LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(v_00_u03b1_1445_, v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
    lean_dec(v___y_1450_);
    lean_dec_ref(v___y_1449_);
    lean_dec(v___y_1448_);
    lean_dec_ref(v___y_1447_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(
    mut v_k_1453_: *mut LeanObject,
    mut v_b_1454_: *mut LeanObject,
    mut v___y_1455_: *mut LeanObject,
    mut v___y_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1458_);
    lean_inc_ref(v___y_1457_);
    lean_inc(v___y_1456_);
    lean_inc_ref(v___y_1455_);
    v___x_1460_ = lean_apply_6(
        v_k_1453_,
        v_b_1454_,
        v___y_1455_,
        v___y_1456_,
        v___y_1457_,
        v___y_1458_,
        lean_box(0),
    );
    return v___x_1460_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed(
    mut v_k_1461_: *mut LeanObject,
    mut v_b_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
    mut v___y_1465_: *mut LeanObject,
    mut v___y_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1468_: *mut LeanObject = core::ptr::null_mut();
    v_res_1468_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(v_k_1461_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
    lean_dec(v___y_1466_);
    lean_dec_ref(v___y_1465_);
    lean_dec(v___y_1464_);
    lean_dec_ref(v___y_1463_);
    return v_res_1468_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(
    mut v_name_1469_: *mut LeanObject,
    mut v_bi_1470_: u8,
    mut v_type_1471_: *mut LeanObject,
    mut v_k_1472_: *mut LeanObject,
    mut v_kind_1473_: u8,
    mut v___y_1474_: *mut LeanObject,
    mut v___y_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_a_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1479_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_1479_, 0, v_k_1472_);
                v___x_1480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_1469_,
                    v_bi_1470_,
                    v_type_1471_,
                    v___f_1479_,
                    v_kind_1473_,
                    v___y_1474_,
                    v___y_1475_,
                    v___y_1476_,
                    v___y_1477_,
                );
                if lean_obj_tag(v___x_1480_) == 0 {
                    v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
                    v_isSharedCheck_1488_ = (!lean_is_exclusive(v___x_1480_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1483_ = v___x_1480_;
                        v_isShared_1484_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1481_);
                        lean_dec(v___x_1480_);
                        v___x_1483_ = lean_box(0);
                        v_isShared_1484_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1489_ = lean_ctor_get(v___x_1480_, 0);
                    v_isSharedCheck_1496_ = (!lean_is_exclusive(v___x_1480_)) as u8;
                    if v_isSharedCheck_1496_ == 0 {
                        v___x_1491_ = v___x_1480_;
                        v_isShared_1492_ = v_isSharedCheck_1496_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1489_);
                        lean_dec(v___x_1480_);
                        v___x_1491_ = lean_box(0);
                        v_isShared_1492_ = v_isSharedCheck_1496_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1484_ == 0 {
                    v___x_1486_ = v___x_1483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
                    v___x_1486_ = v_reuseFailAlloc_1487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1486_;
            }
            3 => {
                if v_isShared_1492_ == 0 {
                    v___x_1494_ = v___x_1491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
                    v___x_1494_ = v_reuseFailAlloc_1495_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___boxed(
    mut v_name_1497_: *mut LeanObject,
    mut v_bi_1498_: *mut LeanObject,
    mut v_type_1499_: *mut LeanObject,
    mut v_k_1500_: *mut LeanObject,
    mut v_kind_1501_: *mut LeanObject,
    mut v___y_1502_: *mut LeanObject,
    mut v___y_1503_: *mut LeanObject,
    mut v___y_1504_: *mut LeanObject,
    mut v___y_1505_: *mut LeanObject,
    mut v___y_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_1507_: u8 = 0;
    let mut v_kind_boxed_1508_: u8 = 0;
    let mut v_res_1509_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_1507_ = (lean_unbox(v_bi_1498_) as u8);
    v_kind_boxed_1508_ = (lean_unbox(v_kind_1501_) as u8);
    v_res_1509_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_1497_, v_bi_boxed_1507_, v_type_1499_, v_k_1500_, v_kind_boxed_1508_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
    lean_dec(v___y_1505_);
    lean_dec_ref(v___y_1504_);
    lean_dec(v___y_1503_);
    lean_dec_ref(v___y_1502_);
    return v_res_1509_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(
    mut v_name_1510_: *mut LeanObject,
    mut v_type_1511_: *mut LeanObject,
    mut v_k_1512_: *mut LeanObject,
    mut v___y_1513_: *mut LeanObject,
    mut v___y_1514_: *mut LeanObject,
    mut v___y_1515_: *mut LeanObject,
    mut v___y_1516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: u8 = 0;
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    v___x_1518_ = 0;
    v___x_1519_ = 0;
    v___x_1520_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_1510_, v___x_1518_, v_type_1511_, v_k_1512_, v___x_1519_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
    return v___x_1520_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg___boxed(
    mut v_name_1521_: *mut LeanObject,
    mut v_type_1522_: *mut LeanObject,
    mut v_k_1523_: *mut LeanObject,
    mut v___y_1524_: *mut LeanObject,
    mut v___y_1525_: *mut LeanObject,
    mut v___y_1526_: *mut LeanObject,
    mut v___y_1527_: *mut LeanObject,
    mut v___y_1528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1529_: *mut LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_1521_, v_type_1522_, v_k_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
    lean_dec(v___y_1527_);
    lean_dec_ref(v___y_1526_);
    lean_dec(v___y_1525_);
    lean_dec_ref(v___y_1524_);
    return v_res_1529_;
}
pub unsafe fn _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    v___x_1533_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2;
    v___x_1534_ = lean_unsigned_to_nat(8);
    v___x_1535_ = lean_unsigned_to_nat(91);
    v___x_1536_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1;
    v___x_1537_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0;
    v___x_1538_ = l_mkPanicMessageWithDecl(
        v___x_1537_,
        v___x_1536_,
        v___x_1535_,
        v___x_1534_,
        v___x_1533_,
    );
    return v___x_1538_;
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed(
    mut v_zs2_1539_: *mut LeanObject,
    mut v_acc_1540_: *mut LeanObject,
    mut v_ctor_1541_: *mut LeanObject,
    mut v_k_1542_: *mut LeanObject,
    mut v_zs_1543_: *mut LeanObject,
    mut v_indices_1544_: *mut LeanObject,
    mut v_tail_1545_: *mut LeanObject,
    mut v_tail_1546_: *mut LeanObject,
    mut v_z_x27_1547_: *mut LeanObject,
    mut v___y_1548_: *mut LeanObject,
    mut v___y_1549_: *mut LeanObject,
    mut v___y_1550_: *mut LeanObject,
    mut v___y_1551_: *mut LeanObject,
    mut v___y_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1553_: *mut LeanObject = core::ptr::null_mut();
    v_res_1553_ =
        l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(
            v_zs2_1539_,
            v_acc_1540_,
            v_ctor_1541_,
            v_k_1542_,
            v_zs_1543_,
            v_indices_1544_,
            v_tail_1545_,
            v_tail_1546_,
            v_z_x27_1547_,
            v___y_1548_,
            v___y_1549_,
            v___y_1550_,
            v___y_1551_,
        );
    lean_dec(v___y_1551_);
    lean_dec_ref(v___y_1550_);
    lean_dec(v___y_1549_);
    lean_dec_ref(v___y_1548_);
    return v_res_1553_;
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(
    mut v_ctor_1555_: *mut LeanObject,
    mut v_k_1556_: *mut LeanObject,
    mut v_zs_1557_: *mut LeanObject,
    mut v_indices_1558_: *mut LeanObject,
    mut v_zs2_1559_: *mut LeanObject,
    mut v_mask_1560_: *mut LeanObject,
    mut v_todo_1561_: *mut LeanObject,
    mut v_acc_1562_: *mut LeanObject,
    mut v_a_1563_: *mut LeanObject,
    mut v_a_1564_: *mut LeanObject,
    mut v_a_1565_: *mut LeanObject,
    mut v_a_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v_tail_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u8 = 0;
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1589_: u8 = 0;
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut v_a_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_mask_1560_) == 1 {
                    v_head_1568_ = lean_ctor_get(v_mask_1560_, 0);
                    v___x_1569_ = (lean_unbox(v_head_1568_) as u8);
                    if v___x_1569_ == 0 {
                        if lean_obj_tag(v_todo_1561_) == 1 {
                            v_tail_1570_ = lean_ctor_get(v_mask_1560_, 1);
                            lean_inc(v_tail_1570_);
                            lean_dec_ref_known(v_mask_1560_, 2);
                            v_tail_1571_ = lean_ctor_get(v_todo_1561_, 1);
                            lean_inc(v_tail_1571_);
                            lean_dec_ref_known(v_todo_1561_, 2);
                            lean_inc_ref(v_ctor_1555_);
                            v___x_1572_ = l_Lean_mkAppN(v_ctor_1555_, v_zs2_1559_);
                            lean_inc(v_a_1566_);
                            lean_inc_ref(v_a_1565_);
                            lean_inc(v_a_1564_);
                            lean_inc_ref(v_a_1563_);
                            v___x_1573_ = lean_infer_type(
                                v___x_1572_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                            );
                            if lean_obj_tag(v___x_1573_) == 0 {
                                v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
                                lean_inc(v_a_1574_);
                                lean_dec_ref_known(v___x_1573_, 1);
                                v___x_1575_ = l_Lean_Meta_whnfForall(
                                    v_a_1574_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_,
                                );
                                if lean_obj_tag(v___x_1575_) == 0 {
                                    v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
                                    lean_inc(v_a_1576_);
                                    lean_dec_ref_known(v___x_1575_, 1);
                                    v___x_1577_ = l_Lean_Expr_isForall(v_a_1576_);
                                    if v___x_1577_ == 0 {
                                        lean_dec(v_a_1576_);
                                        lean_dec(v_tail_1571_);
                                        lean_dec(v_tail_1570_);
                                        lean_dec_ref(v_acc_1562_);
                                        lean_dec_ref(v_zs2_1559_);
                                        lean_dec_ref(v_indices_1558_);
                                        lean_dec_ref(v_zs_1557_);
                                        lean_dec_ref(v_k_1556_);
                                        lean_dec_ref(v_ctor_1555_);
                                        v___x_1578_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once), _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3);
                                        v___x_1579_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v___x_1578_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
                                        return v___x_1579_;
                                    } else {
                                        v___f_1580_ = lean_alloc_closure(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 8);
                                        lean_closure_set(v___f_1580_, 0, v_zs2_1559_);
                                        lean_closure_set(v___f_1580_, 1, v_acc_1562_);
                                        lean_closure_set(v___f_1580_, 2, v_ctor_1555_);
                                        lean_closure_set(v___f_1580_, 3, v_k_1556_);
                                        lean_closure_set(v___f_1580_, 4, v_zs_1557_);
                                        lean_closure_set(v___f_1580_, 5, v_indices_1558_);
                                        lean_closure_set(v___f_1580_, 6, v_tail_1570_);
                                        lean_closure_set(v___f_1580_, 7, v_tail_1571_);
                                        v___x_1581_ = l_Lean_Expr_bindingName_x21(v_a_1576_);
                                        v___x_1582_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4;
                                        v___x_1583_ =
                                            lean_name_append_after(v___x_1581_, v___x_1582_);
                                        v___x_1584_ = l_Lean_Expr_bindingDomain_x21(v_a_1576_);
                                        lean_dec(v_a_1576_);
                                        v___x_1585_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v___x_1583_, v___x_1584_, v___f_1580_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
                                        return v___x_1585_;
                                    }
                                } else {
                                    lean_dec(v_tail_1571_);
                                    lean_dec(v_tail_1570_);
                                    lean_dec_ref(v_acc_1562_);
                                    lean_dec_ref(v_zs2_1559_);
                                    lean_dec_ref(v_indices_1558_);
                                    lean_dec_ref(v_zs_1557_);
                                    lean_dec_ref(v_k_1556_);
                                    lean_dec_ref(v_ctor_1555_);
                                    v_a_1586_ = lean_ctor_get(v___x_1575_, 0);
                                    v_isSharedCheck_1593_ = (!lean_is_exclusive(v___x_1575_)) as u8;
                                    if v_isSharedCheck_1593_ == 0 {
                                        v___x_1588_ = v___x_1575_;
                                        v_isShared_1589_ = v_isSharedCheck_1593_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1586_);
                                        lean_dec(v___x_1575_);
                                        v___x_1588_ = lean_box(0);
                                        v_isShared_1589_ = v_isSharedCheck_1593_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_tail_1571_);
                                lean_dec(v_tail_1570_);
                                lean_dec_ref(v_acc_1562_);
                                lean_dec_ref(v_zs2_1559_);
                                lean_dec_ref(v_indices_1558_);
                                lean_dec_ref(v_zs_1557_);
                                lean_dec_ref(v_k_1556_);
                                lean_dec_ref(v_ctor_1555_);
                                v_a_1594_ = lean_ctor_get(v___x_1573_, 0);
                                v_isSharedCheck_1601_ = (!lean_is_exclusive(v___x_1573_)) as u8;
                                if v_isSharedCheck_1601_ == 0 {
                                    v___x_1596_ = v___x_1573_;
                                    v_isShared_1597_ = v_isSharedCheck_1601_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_1594_);
                                    lean_dec(v___x_1573_);
                                    v___x_1596_ = lean_box(0);
                                    v_isShared_1597_ = v_isSharedCheck_1601_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_mask_1560_, 2);
                            lean_dec(v_todo_1561_);
                            lean_dec_ref(v_ctor_1555_);
                            lean_inc(v_a_1566_);
                            lean_inc_ref(v_a_1565_);
                            lean_inc(v_a_1564_);
                            lean_inc_ref(v_a_1563_);
                            v___x_1602_ = lean_apply_9(
                                v_k_1556_,
                                v_acc_1562_,
                                v_indices_1558_,
                                v_zs_1557_,
                                v_zs2_1559_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                                lean_box(0),
                            );
                            return v___x_1602_;
                        }
                    } else {
                        if lean_obj_tag(v_todo_1561_) == 1 {
                            v_tail_1603_ = lean_ctor_get(v_mask_1560_, 1);
                            lean_inc(v_tail_1603_);
                            lean_dec_ref_known(v_mask_1560_, 2);
                            v_head_1604_ = lean_ctor_get(v_todo_1561_, 0);
                            lean_inc(v_head_1604_);
                            v_tail_1605_ = lean_ctor_get(v_todo_1561_, 1);
                            lean_inc(v_tail_1605_);
                            lean_dec_ref_known(v_todo_1561_, 2);
                            v___x_1606_ = lean_array_push(v_zs2_1559_, v_head_1604_);
                            v_zs2_1559_ = v___x_1606_;
                            v_mask_1560_ = v_tail_1603_;
                            v_todo_1561_ = v_tail_1605_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref_known(v_mask_1560_, 2);
                            lean_dec(v_todo_1561_);
                            lean_dec_ref(v_ctor_1555_);
                            lean_inc(v_a_1566_);
                            lean_inc_ref(v_a_1565_);
                            lean_inc(v_a_1564_);
                            lean_inc_ref(v_a_1563_);
                            v___x_1608_ = lean_apply_9(
                                v_k_1556_,
                                v_acc_1562_,
                                v_indices_1558_,
                                v_zs_1557_,
                                v_zs2_1559_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                                lean_box(0),
                            );
                            return v___x_1608_;
                        }
                    }
                } else {
                    lean_dec(v_todo_1561_);
                    lean_dec(v_mask_1560_);
                    lean_dec_ref(v_ctor_1555_);
                    lean_inc(v_a_1566_);
                    lean_inc_ref(v_a_1565_);
                    lean_inc(v_a_1564_);
                    lean_inc_ref(v_a_1563_);
                    v___x_1609_ = lean_apply_9(
                        v_k_1556_,
                        v_acc_1562_,
                        v_indices_1558_,
                        v_zs_1557_,
                        v_zs2_1559_,
                        v_a_1563_,
                        v_a_1564_,
                        v_a_1565_,
                        v_a_1566_,
                        lean_box(0),
                    );
                    return v___x_1609_;
                }
            }
            1 => {
                if v_isShared_1589_ == 0 {
                    v___x_1591_ = v___x_1588_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
                    v___x_1591_ = v_reuseFailAlloc_1592_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1591_;
            }
            3 => {
                if v_isShared_1597_ == 0 {
                    v___x_1599_ = v___x_1596_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
                    v___x_1599_ = v_reuseFailAlloc_1600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(
    mut v_zs2_1610_: *mut LeanObject,
    mut v_acc_1611_: *mut LeanObject,
    mut v_ctor_1612_: *mut LeanObject,
    mut v_k_1613_: *mut LeanObject,
    mut v_zs_1614_: *mut LeanObject,
    mut v_indices_1615_: *mut LeanObject,
    mut v_tail_1616_: *mut LeanObject,
    mut v_tail_1617_: *mut LeanObject,
    mut v_z_x27_1618_: *mut LeanObject,
    mut v___y_1619_: *mut LeanObject,
    mut v___y_1620_: *mut LeanObject,
    mut v___y_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_z_x27_1618_);
    v___x_1624_ = lean_array_push(v_zs2_1610_, v_z_x27_1618_);
    v___x_1625_ = lean_array_push(v_acc_1611_, v_z_x27_1618_);
    v___x_1626_ =
        l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(
            v_ctor_1612_,
            v_k_1613_,
            v_zs_1614_,
            v_indices_1615_,
            v___x_1624_,
            v_tail_1616_,
            v_tail_1617_,
            v___x_1625_,
            v___y_1619_,
            v___y_1620_,
            v___y_1621_,
            v___y_1622_,
        );
    return v___x_1626_;
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___boxed(
    mut v_ctor_1627_: *mut LeanObject,
    mut v_k_1628_: *mut LeanObject,
    mut v_zs_1629_: *mut LeanObject,
    mut v_indices_1630_: *mut LeanObject,
    mut v_zs2_1631_: *mut LeanObject,
    mut v_mask_1632_: *mut LeanObject,
    mut v_todo_1633_: *mut LeanObject,
    mut v_acc_1634_: *mut LeanObject,
    mut v_a_1635_: *mut LeanObject,
    mut v_a_1636_: *mut LeanObject,
    mut v_a_1637_: *mut LeanObject,
    mut v_a_1638_: *mut LeanObject,
    mut v_a_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1640_: *mut LeanObject = core::ptr::null_mut();
    v_res_1640_ =
        l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(
            v_ctor_1627_,
            v_k_1628_,
            v_zs_1629_,
            v_indices_1630_,
            v_zs2_1631_,
            v_mask_1632_,
            v_todo_1633_,
            v_acc_1634_,
            v_a_1635_,
            v_a_1636_,
            v_a_1637_,
            v_a_1638_,
        );
    lean_dec(v_a_1638_);
    lean_dec_ref(v_a_1637_);
    lean_dec(v_a_1636_);
    lean_dec_ref(v_a_1635_);
    return v_res_1640_;
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(
    mut v_00_u03b1_1641_: *mut LeanObject,
    mut v_ctor_1642_: *mut LeanObject,
    mut v_k_1643_: *mut LeanObject,
    mut v_zs_1644_: *mut LeanObject,
    mut v_indices_1645_: *mut LeanObject,
    mut v_zs2_1646_: *mut LeanObject,
    mut v_mask_1647_: *mut LeanObject,
    mut v_todo_1648_: *mut LeanObject,
    mut v_acc_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
    mut v_a_1651_: *mut LeanObject,
    mut v_a_1652_: *mut LeanObject,
    mut v_a_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    v___x_1655_ =
        l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(
            v_ctor_1642_,
            v_k_1643_,
            v_zs_1644_,
            v_indices_1645_,
            v_zs2_1646_,
            v_mask_1647_,
            v_todo_1648_,
            v_acc_1649_,
            v_a_1650_,
            v_a_1651_,
            v_a_1652_,
            v_a_1653_,
        );
    return v___x_1655_;
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___boxed(
    mut v_00_u03b1_1656_: *mut LeanObject,
    mut v_ctor_1657_: *mut LeanObject,
    mut v_k_1658_: *mut LeanObject,
    mut v_zs_1659_: *mut LeanObject,
    mut v_indices_1660_: *mut LeanObject,
    mut v_zs2_1661_: *mut LeanObject,
    mut v_mask_1662_: *mut LeanObject,
    mut v_todo_1663_: *mut LeanObject,
    mut v_acc_1664_: *mut LeanObject,
    mut v_a_1665_: *mut LeanObject,
    mut v_a_1666_: *mut LeanObject,
    mut v_a_1667_: *mut LeanObject,
    mut v_a_1668_: *mut LeanObject,
    mut v_a_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1670_: *mut LeanObject = core::ptr::null_mut();
    v_res_1670_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(
        v_00_u03b1_1656_,
        v_ctor_1657_,
        v_k_1658_,
        v_zs_1659_,
        v_indices_1660_,
        v_zs2_1661_,
        v_mask_1662_,
        v_todo_1663_,
        v_acc_1664_,
        v_a_1665_,
        v_a_1666_,
        v_a_1667_,
        v_a_1668_,
    );
    lean_dec(v_a_1668_);
    lean_dec_ref(v_a_1667_);
    lean_dec(v_a_1666_);
    lean_dec_ref(v_a_1665_);
    return v_res_1670_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(
    mut v_00_u03b1_1671_: *mut LeanObject,
    mut v_name_1672_: *mut LeanObject,
    mut v_bi_1673_: u8,
    mut v_type_1674_: *mut LeanObject,
    mut v_k_1675_: *mut LeanObject,
    mut v_kind_1676_: u8,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    v___x_1682_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_1672_, v_bi_1673_, v_type_1674_, v_k_1675_, v_kind_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
    return v___x_1682_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___boxed(
    mut v_00_u03b1_1683_: *mut LeanObject,
    mut v_name_1684_: *mut LeanObject,
    mut v_bi_1685_: *mut LeanObject,
    mut v_type_1686_: *mut LeanObject,
    mut v_k_1687_: *mut LeanObject,
    mut v_kind_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_1694_: u8 = 0;
    let mut v_kind_boxed_1695_: u8 = 0;
    let mut v_res_1696_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_1694_ = (lean_unbox(v_bi_1685_) as u8);
    v_kind_boxed_1695_ = (lean_unbox(v_kind_1688_) as u8);
    v_res_1696_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(v_00_u03b1_1683_, v_name_1684_, v_bi_boxed_1694_, v_type_1686_, v_k_1687_, v_kind_boxed_1695_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
    lean_dec(v___y_1692_);
    lean_dec_ref(v___y_1691_);
    lean_dec(v___y_1690_);
    lean_dec_ref(v___y_1689_);
    return v_res_1696_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(
    mut v_00_u03b1_1697_: *mut LeanObject,
    mut v_name_1698_: *mut LeanObject,
    mut v_type_1699_: *mut LeanObject,
    mut v_k_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_1698_, v_type_1699_, v_k_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___boxed(
    mut v_00_u03b1_1707_: *mut LeanObject,
    mut v_name_1708_: *mut LeanObject,
    mut v_type_1709_: *mut LeanObject,
    mut v_k_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
    mut v___y_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1716_: *mut LeanObject = core::ptr::null_mut();
    v_res_1716_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(v_00_u03b1_1707_, v_name_1708_, v_type_1709_, v_k_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
    lean_dec(v___y_1714_);
    lean_dec_ref(v___y_1713_);
    lean_dec(v___y_1712_);
    lean_dec_ref(v___y_1711_);
    return v_res_1716_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(
    mut v_type_1717_: *mut LeanObject,
    mut v_k_1718_: *mut LeanObject,
    mut v_cleanupAnnotations_1719_: u8,
    mut v_whnfType_1720_: u8,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut v_a_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1726_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_1726_, 0, v_k_1718_);
                v___x_1727_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_1717_,
                    v___f_1726_,
                    v_cleanupAnnotations_1719_,
                    v_whnfType_1720_,
                    v___y_1721_,
                    v___y_1722_,
                    v___y_1723_,
                    v___y_1724_,
                );
                if lean_obj_tag(v___x_1727_) == 0 {
                    v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
                    v_isSharedCheck_1735_ = (!lean_is_exclusive(v___x_1727_)) as u8;
                    if v_isSharedCheck_1735_ == 0 {
                        v___x_1730_ = v___x_1727_;
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1728_);
                        lean_dec(v___x_1727_);
                        v___x_1730_ = lean_box(0);
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1736_ = lean_ctor_get(v___x_1727_, 0);
                    v_isSharedCheck_1743_ = (!lean_is_exclusive(v___x_1727_)) as u8;
                    if v_isSharedCheck_1743_ == 0 {
                        v___x_1738_ = v___x_1727_;
                        v_isShared_1739_ = v_isSharedCheck_1743_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1736_);
                        lean_dec(v___x_1727_);
                        v___x_1738_ = lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1743_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1731_ == 0 {
                    v___x_1733_ = v___x_1730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1733_;
            }
            3 => {
                if v_isShared_1739_ == 0 {
                    v___x_1741_ = v___x_1738_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
                    v___x_1741_ = v_reuseFailAlloc_1742_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg___boxed(
    mut v_type_1744_: *mut LeanObject,
    mut v_k_1745_: *mut LeanObject,
    mut v_cleanupAnnotations_1746_: *mut LeanObject,
    mut v_whnfType_1747_: *mut LeanObject,
    mut v___y_1748_: *mut LeanObject,
    mut v___y_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1753_: u8 = 0;
    let mut v_whnfType_boxed_1754_: u8 = 0;
    let mut v_res_1755_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1753_ = (lean_unbox(v_cleanupAnnotations_1746_) as u8);
    v_whnfType_boxed_1754_ = (lean_unbox(v_whnfType_1747_) as u8);
    v_res_1755_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_1744_, v_k_1745_, v_cleanupAnnotations_boxed_1753_, v_whnfType_boxed_1754_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
    lean_dec(v___y_1751_);
    lean_dec_ref(v___y_1750_);
    lean_dec(v___y_1749_);
    lean_dec_ref(v___y_1748_);
    return v_res_1755_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(
    mut v_00_u03b1_1756_: *mut LeanObject,
    mut v_type_1757_: *mut LeanObject,
    mut v_k_1758_: *mut LeanObject,
    mut v_cleanupAnnotations_1759_: u8,
    mut v_whnfType_1760_: u8,
    mut v___y_1761_: *mut LeanObject,
    mut v___y_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
    mut v___y_1764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    v___x_1766_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_1757_, v_k_1758_, v_cleanupAnnotations_1759_, v_whnfType_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
    return v___x_1766_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___boxed(
    mut v_00_u03b1_1767_: *mut LeanObject,
    mut v_type_1768_: *mut LeanObject,
    mut v_k_1769_: *mut LeanObject,
    mut v_cleanupAnnotations_1770_: *mut LeanObject,
    mut v_whnfType_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
    mut v___y_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
    mut v___y_1775_: *mut LeanObject,
    mut v___y_1776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1777_: u8 = 0;
    let mut v_whnfType_boxed_1778_: u8 = 0;
    let mut v_res_1779_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1777_ = (lean_unbox(v_cleanupAnnotations_1770_) as u8);
    v_whnfType_boxed_1778_ = (lean_unbox(v_whnfType_1771_) as u8);
    v_res_1779_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(
            v_00_u03b1_1767_,
            v_type_1768_,
            v_k_1769_,
            v_cleanupAnnotations_boxed_1777_,
            v_whnfType_boxed_1778_,
            v___y_1772_,
            v___y_1773_,
            v___y_1774_,
            v___y_1775_,
        );
    lean_dec(v___y_1775_);
    lean_dec_ref(v___y_1774_);
    lean_dec(v___y_1773_);
    lean_dec_ref(v___y_1772_);
    return v_res_1779_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    v___x_1781_ =
        l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0;
    v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
    return v___x_1782_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(
    mut v_constName_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1789_ = lean_st_ref_get(v___y_1787_);
                v_env_1790_ = lean_ctor_get(v___x_1789_, 0);
                lean_inc_ref(v_env_1790_);
                lean_dec(v___x_1789_);
                lean_inc(v_constName_1783_);
                v___x_1791_ = l_Lean_isInductiveCore_x3f(v_env_1790_, v_constName_1783_);
                if lean_obj_tag(v___x_1791_) == 0 {
                    v___x_1792_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
                    v___x_1793_ = 0;
                    v___x_1794_ = l_Lean_MessageData_ofConstName(v_constName_1783_, v___x_1793_);
                    v___x_1795_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1795_, 0, v___x_1792_);
                    lean_ctor_set(v___x_1795_, 1, v___x_1794_);
                    v___x_1796_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1);
                    v___x_1797_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1797_, 0, v___x_1795_);
                    lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                    v___x_1798_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_1797_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
                    return v___x_1798_;
                } else {
                    lean_dec(v_constName_1783_);
                    v_val_1799_ = lean_ctor_get(v___x_1791_, 0);
                    v_isSharedCheck_1806_ = (!lean_is_exclusive(v___x_1791_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v___x_1801_ = v___x_1791_;
                        v_isShared_1802_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1799_);
                        lean_dec(v___x_1791_);
                        v___x_1801_ = lean_box(0);
                        v_isShared_1802_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1802_ == 0 {
                    lean_ctor_set_tag(v___x_1801_, 0);
                    v___x_1804_ = v___x_1801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_val_1799_);
                    v___x_1804_ = v_reuseFailAlloc_1805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___boxed(
    mut v_constName_1807_: *mut LeanObject,
    mut v___y_1808_: *mut LeanObject,
    mut v___y_1809_: *mut LeanObject,
    mut v___y_1810_: *mut LeanObject,
    mut v___y_1811_: *mut LeanObject,
    mut v___y_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1813_: *mut LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(
        v_constName_1807_,
        v___y_1808_,
        v___y_1809_,
        v___y_1810_,
        v___y_1811_,
    );
    lean_dec(v___y_1811_);
    lean_dec_ref(v___y_1810_);
    lean_dec(v___y_1809_);
    lean_dec_ref(v___y_1808_);
    return v_res_1813_;
}
pub unsafe fn _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1815_: *mut LeanObject = core::ptr::null_mut();
    v___x_1814_ = lean_box(0);
    v_dummy_1815_ = l_Lean_Expr_sort___override(v___x_1814_);
    return v_dummy_1815_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(
    mut v_ctor_1818_: *mut LeanObject,
    mut v_k_1819_: *mut LeanObject,
    mut v_zs_1820_: *mut LeanObject,
    mut v_ctorRet_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
    mut v___y_1823_: *mut LeanObject,
    mut v___y_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1854_: u8 = 0;
    let mut v_a_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_a_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_a_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1825_);
                lean_inc_ref(v___y_1824_);
                lean_inc(v___y_1823_);
                lean_inc_ref(v___y_1822_);
                v___x_1827_ = lean_whnf(
                    v_ctorRet_1821_,
                    v___y_1822_,
                    v___y_1823_,
                    v___y_1824_,
                    v___y_1825_,
                );
                if lean_obj_tag(v___x_1827_) == 0 {
                    v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
                    lean_inc(v_a_1828_);
                    lean_dec_ref_known(v___x_1827_, 1);
                    v___x_1829_ = l_Lean_Core_betaReduce(v_a_1828_, v___y_1824_, v___y_1825_);
                    if lean_obj_tag(v___x_1829_) == 0 {
                        v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
                        lean_inc(v_a_1830_);
                        lean_dec_ref_known(v___x_1829_, 1);
                        v___x_1831_ = l_Lean_Expr_getAppFn(v_a_1830_);
                        v___x_1832_ = l_Lean_Expr_constName_x21(v___x_1831_);
                        lean_dec_ref(v___x_1831_);
                        v___x_1833_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v___x_1832_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
                        if lean_obj_tag(v___x_1833_) == 0 {
                            v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
                            lean_inc(v_a_1834_);
                            lean_dec_ref_known(v___x_1833_, 1);
                            v_numIndices_1835_ = lean_ctor_get(v_a_1834_, 2);
                            lean_inc(v_numIndices_1835_);
                            lean_dec(v_a_1834_);
                            v___x_1836_ = l_Lean_Expr_getAppFn(v_ctor_1818_);
                            v___x_1837_ = l_Lean_Expr_constName_x21(v___x_1836_);
                            lean_dec_ref(v___x_1836_);
                            v___x_1838_ = l_Lean_Meta_occursInCtorTypeMask(
                                v___x_1837_,
                                v___y_1822_,
                                v___y_1823_,
                                v___y_1824_,
                                v___y_1825_,
                            );
                            if lean_obj_tag(v___x_1838_) == 0 {
                                v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
                                lean_inc(v_a_1839_);
                                lean_dec_ref_known(v___x_1838_, 1);
                                v_dummy_1840_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once), _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0);
                                lean_inc(v_numIndices_1835_);
                                v___x_1841_ = lean_mk_array(v_numIndices_1835_, v_dummy_1840_);
                                v___x_1842_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(
                                    v_numIndices_1835_,
                                    v_a_1830_,
                                    v___x_1841_,
                                );
                                v___x_1843_ =
                                    l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1;
                                v___x_1844_ = lean_array_to_list(v_a_1839_);
                                lean_inc_ref_n(v_zs_1820_, 2);
                                v___x_1845_ = lean_array_to_list(v_zs_1820_);
                                v___x_1846_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_1818_, v_k_1819_, v_zs_1820_, v___x_1842_, v___x_1843_, v___x_1844_, v___x_1845_, v_zs_1820_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
                                return v___x_1846_;
                            } else {
                                lean_dec(v_numIndices_1835_);
                                lean_dec(v_a_1830_);
                                lean_dec_ref(v_zs_1820_);
                                lean_dec_ref(v_k_1819_);
                                lean_dec_ref(v_ctor_1818_);
                                v_a_1847_ = lean_ctor_get(v___x_1838_, 0);
                                v_isSharedCheck_1854_ = (!lean_is_exclusive(v___x_1838_)) as u8;
                                if v_isSharedCheck_1854_ == 0 {
                                    v___x_1849_ = v___x_1838_;
                                    v_isShared_1850_ = v_isSharedCheck_1854_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_1847_);
                                    lean_dec(v___x_1838_);
                                    v___x_1849_ = lean_box(0);
                                    v_isShared_1850_ = v_isSharedCheck_1854_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_1830_);
                            lean_dec_ref(v_zs_1820_);
                            lean_dec_ref(v_k_1819_);
                            lean_dec_ref(v_ctor_1818_);
                            v_a_1855_ = lean_ctor_get(v___x_1833_, 0);
                            v_isSharedCheck_1862_ = (!lean_is_exclusive(v___x_1833_)) as u8;
                            if v_isSharedCheck_1862_ == 0 {
                                v___x_1857_ = v___x_1833_;
                                v_isShared_1858_ = v_isSharedCheck_1862_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1855_);
                                lean_dec(v___x_1833_);
                                v___x_1857_ = lean_box(0);
                                v_isShared_1858_ = v_isSharedCheck_1862_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_zs_1820_);
                        lean_dec_ref(v_k_1819_);
                        lean_dec_ref(v_ctor_1818_);
                        v_a_1863_ = lean_ctor_get(v___x_1829_, 0);
                        v_isSharedCheck_1870_ = (!lean_is_exclusive(v___x_1829_)) as u8;
                        if v_isSharedCheck_1870_ == 0 {
                            v___x_1865_ = v___x_1829_;
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1863_);
                            lean_dec(v___x_1829_);
                            v___x_1865_ = lean_box(0);
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_zs_1820_);
                    lean_dec_ref(v_k_1819_);
                    lean_dec_ref(v_ctor_1818_);
                    v_a_1871_ = lean_ctor_get(v___x_1827_, 0);
                    v_isSharedCheck_1878_ = (!lean_is_exclusive(v___x_1827_)) as u8;
                    if v_isSharedCheck_1878_ == 0 {
                        v___x_1873_ = v___x_1827_;
                        v_isShared_1874_ = v_isSharedCheck_1878_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1871_);
                        lean_dec(v___x_1827_);
                        v___x_1873_ = lean_box(0);
                        v_isShared_1874_ = v_isSharedCheck_1878_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1850_ == 0 {
                    v___x_1852_ = v___x_1849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
                    v___x_1852_ = v_reuseFailAlloc_1853_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1852_;
            }
            3 => {
                if v_isShared_1858_ == 0 {
                    v___x_1860_ = v___x_1857_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
                    v___x_1860_ = v_reuseFailAlloc_1861_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1860_;
            }
            5 => {
                if v_isShared_1866_ == 0 {
                    v___x_1868_ = v___x_1865_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1868_;
            }
            7 => {
                if v_isShared_1874_ == 0 {
                    v___x_1876_ = v___x_1873_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
                    v___x_1876_ = v_reuseFailAlloc_1877_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed(
    mut v_ctor_1879_: *mut LeanObject,
    mut v_k_1880_: *mut LeanObject,
    mut v_zs_1881_: *mut LeanObject,
    mut v_ctorRet_1882_: *mut LeanObject,
    mut v___y_1883_: *mut LeanObject,
    mut v___y_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1888_: *mut LeanObject = core::ptr::null_mut();
    v_res_1888_ = l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(
        v_ctor_1879_,
        v_k_1880_,
        v_zs_1881_,
        v_ctorRet_1882_,
        v___y_1883_,
        v___y_1884_,
        v___y_1885_,
        v___y_1886_,
    );
    lean_dec(v___y_1886_);
    lean_dec_ref(v___y_1885_);
    lean_dec(v___y_1884_);
    lean_dec_ref(v___y_1883_);
    return v_res_1888_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices___redArg(
    mut v_ctor_1889_: *mut LeanObject,
    mut v_k_1890_: *mut LeanObject,
    mut v_a_1891_: *mut LeanObject,
    mut v_a_1892_: *mut LeanObject,
    mut v_a_1893_: *mut LeanObject,
    mut v_a_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: u8 = 0;
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_1894_);
                lean_inc_ref(v_a_1893_);
                lean_inc(v_a_1892_);
                lean_inc_ref(v_a_1891_);
                lean_inc_ref(v_ctor_1889_);
                v___x_1896_ =
                    lean_infer_type(v_ctor_1889_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
                if lean_obj_tag(v___x_1896_) == 0 {
                    v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
                    lean_inc(v_a_1897_);
                    lean_dec_ref_known(v___x_1896_, 1);
                    v___f_1898_ = lean_alloc_closure(
                        l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___f_1898_, 0, v_ctor_1889_);
                    lean_closure_set(v___f_1898_, 1, v_k_1890_);
                    v___x_1899_ = 0;
                    v___x_1900_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_a_1897_, v___f_1898_, v___x_1899_, v___x_1899_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
                    return v___x_1900_;
                } else {
                    lean_dec_ref(v_k_1890_);
                    lean_dec_ref(v_ctor_1889_);
                    v_a_1901_ = lean_ctor_get(v___x_1896_, 0);
                    v_isSharedCheck_1908_ = (!lean_is_exclusive(v___x_1896_)) as u8;
                    if v_isSharedCheck_1908_ == 0 {
                        v___x_1903_ = v___x_1896_;
                        v_isShared_1904_ = v_isSharedCheck_1908_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1901_);
                        lean_dec(v___x_1896_);
                        v___x_1903_ = lean_box(0);
                        v_isShared_1904_ = v_isSharedCheck_1908_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1904_ == 0 {
                    v___x_1906_ = v___x_1903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
                    v___x_1906_ = v_reuseFailAlloc_1907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices___redArg___boxed(
    mut v_ctor_1909_: *mut LeanObject,
    mut v_k_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
    mut v_a_1912_: *mut LeanObject,
    mut v_a_1913_: *mut LeanObject,
    mut v_a_1914_: *mut LeanObject,
    mut v_a_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1916_: *mut LeanObject = core::ptr::null_mut();
    v_res_1916_ = l_Lean_Meta_withSharedCtorIndices___redArg(
        v_ctor_1909_,
        v_k_1910_,
        v_a_1911_,
        v_a_1912_,
        v_a_1913_,
        v_a_1914_,
    );
    lean_dec(v_a_1914_);
    lean_dec_ref(v_a_1913_);
    lean_dec(v_a_1912_);
    lean_dec_ref(v_a_1911_);
    return v_res_1916_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices(
    mut v_00_u03b1_1917_: *mut LeanObject,
    mut v_ctor_1918_: *mut LeanObject,
    mut v_k_1919_: *mut LeanObject,
    mut v_a_1920_: *mut LeanObject,
    mut v_a_1921_: *mut LeanObject,
    mut v_a_1922_: *mut LeanObject,
    mut v_a_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    v___x_1925_ = l_Lean_Meta_withSharedCtorIndices___redArg(
        v_ctor_1918_,
        v_k_1919_,
        v_a_1920_,
        v_a_1921_,
        v_a_1922_,
        v_a_1923_,
    );
    return v___x_1925_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices___boxed(
    mut v_00_u03b1_1926_: *mut LeanObject,
    mut v_ctor_1927_: *mut LeanObject,
    mut v_k_1928_: *mut LeanObject,
    mut v_a_1929_: *mut LeanObject,
    mut v_a_1930_: *mut LeanObject,
    mut v_a_1931_: *mut LeanObject,
    mut v_a_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1934_: *mut LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Lean_Meta_withSharedCtorIndices(
        v_00_u03b1_1926_,
        v_ctor_1927_,
        v_k_1928_,
        v_a_1929_,
        v_a_1930_,
        v_a_1931_,
        v_a_1932_,
    );
    lean_dec(v_a_1932_);
    lean_dec_ref(v_a_1931_);
    lean_dec(v_a_1930_);
    lean_dec_ref(v_a_1929_);
    return v_res_1934_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_SameCtorUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_SameCtorUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_SameCtorUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_SameCtorUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_SameCtorUtils(builtin);
}
