// Lean compiler output
// Module: Lean.Meta.SameCtorUtils
// Imports: Lean.Meta.Basic Lean.Meta.Transform
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget, lean_array_uset,
    lean_expr_eqv, lean_find_expr, lean_infer_type, lean_mk_array, lean_panic_fn_borrowed,
    lean_st_ref_get, lean_usize_add, lean_usize_dec_lt, lean_whnf,
};
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
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_occursInCtorTypeMask___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_occursInCtorTypeMask___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_occursInCtorTypeMask___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value: leanh::LeanStringObject<41> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 116, 46, 105, 115, 70, 111, 114, 97, 108, 108, 10, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value: leanh::LeanStringObject<70> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 97, 109, 101, 67, 116, 111, 114, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 119, 105, 116, 104, 83, 104, 97, 114, 101, 100, 67, 116, 111, 114, 73, 110, 100, 105, 99, 101, 115, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 97, 109, 101, 67, 116, 111, 114, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(
    mut v_lctx_968_: *mut leanh::LeanObject,
    mut v_e_969_: *mut leanh::LeanObject,
    mut v_s_970_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_s_970_) == 1 {
        let mut v_fvarId_971_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_fvarId_971_ = leanh::lean_ctor_get(v_s_970_, 0);
        leanh::lean_inc(v_fvarId_971_);
        v___x_972_ = lean_local_ctx_find(v_lctx_968_, v_fvarId_971_);
        if leanh::lean_obj_tag(v___x_972_) == 1 {
            let mut v_val_973_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_974_: u8 = 0;
            v_val_973_ = leanh::lean_ctor_get(v___x_972_, 0);
            leanh::lean_inc(v_val_973_);
            leanh::lean_dec_ref_known(v___x_972_, 1);
            v___x_974_ = lean_expr_eqv(v_s_970_, v_e_969_);
            leanh::lean_dec_ref_known(v_s_970_, 1);
            if v___x_974_ == 0 {
                let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_976_: u8 = 0;
                v___x_975_ = l_Lean_LocalDecl_type(v_val_973_);
                leanh::lean_dec(v_val_973_);
                v___x_976_ = l_Lean_Expr_occurs(v_e_969_, v___x_975_);
                leanh::lean_dec_ref(v___x_975_);
                return v___x_976_;
            } else {
                leanh::lean_dec(v_val_973_);
                leanh::lean_dec_ref(v_e_969_);
                return v___x_974_;
            }
        } else {
            let mut v___x_977_: u8 = 0;
            leanh::lean_dec(v___x_972_);
            v___x_977_ = lean_expr_eqv(v_s_970_, v_e_969_);
            leanh::lean_dec_ref(v_e_969_);
            leanh::lean_dec_ref_known(v_s_970_, 1);
            return v___x_977_;
        }
    } else {
        let mut v___x_978_: u8 = 0;
        leanh::lean_dec_ref(v_lctx_968_);
        v___x_978_ = lean_expr_eqv(v_s_970_, v_e_969_);
        leanh::lean_dec_ref(v_e_969_);
        leanh::lean_dec_ref(v_s_970_);
        return v___x_978_;
    }
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed(
    mut v_lctx_979_: *mut leanh::LeanObject,
    mut v_e_980_: *mut leanh::LeanObject,
    mut v_s_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_982_: u8 = 0;
    let mut v_r_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(
        v_lctx_979_,
        v_e_980_,
        v_s_981_,
    );
    v_r_983_ = leanh::lean_box((v_res_982_) as usize);
    return v_r_983_;
}
pub unsafe fn l_Lean_Meta_occursOrInType(
    mut v_lctx_984_: *mut leanh::LeanObject,
    mut v_e_985_: *mut leanh::LeanObject,
    mut v_t_986_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_987_, 0, v_lctx_984_);
    leanh::lean_closure_set(v___x_987_, 1, v_e_985_);
    v___x_988_ = lean_find_expr(v___x_987_, v_t_986_);
    leanh::lean_dec_ref(v___x_987_);
    if leanh::lean_obj_tag(v___x_988_) == 0 {
        let mut v___x_989_: u8 = 0;
        v___x_989_ = 0;
        return v___x_989_;
    } else {
        let mut v___x_990_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_988_, 1);
        v___x_990_ = 1;
        return v___x_990_;
    }
}
pub unsafe fn l_Lean_Meta_occursOrInType___boxed(
    mut v_lctx_991_: *mut leanh::LeanObject,
    mut v_e_992_: *mut leanh::LeanObject,
    mut v_t_993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_994_: u8 = 0;
    let mut v_r_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Lean_Meta_occursOrInType(v_lctx_991_, v_e_992_, v_t_993_);
    leanh::lean_dec_ref(v_t_993_);
    v_r_995_ = leanh::lean_box((v_res_994_) as usize);
    return v_r_995_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(
    mut v_k_996_: *mut leanh::LeanObject,
    mut v_b_997_: *mut leanh::LeanObject,
    mut v_c_998_: *mut leanh::LeanObject,
    mut v___y_999_: *mut leanh::LeanObject,
    mut v___y_1000_: *mut leanh::LeanObject,
    mut v___y_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1002_);
    leanh::lean_inc_ref(v___y_1001_);
    leanh::lean_inc(v___y_1000_);
    leanh::lean_inc_ref(v___y_999_);
    v___x_1004_ = leanh::lean_apply_7(
        v_k_996_,
        v_b_997_,
        v_c_998_,
        v___y_999_,
        v___y_1000_,
        v___y_1001_,
        v___y_1002_,
        leanh::lean_box(0),
    );
    return v___x_1004_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed(
    mut v_k_1005_: *mut leanh::LeanObject,
    mut v_b_1006_: *mut leanh::LeanObject,
    mut v_c_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
    mut v___y_1009_: *mut leanh::LeanObject,
    mut v___y_1010_: *mut leanh::LeanObject,
    mut v___y_1011_: *mut leanh::LeanObject,
    mut v___y_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(v_k_1005_, v_b_1006_, v_c_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
    leanh::lean_dec(v___y_1011_);
    leanh::lean_dec_ref(v___y_1010_);
    leanh::lean_dec(v___y_1009_);
    leanh::lean_dec_ref(v___y_1008_);
    return v_res_1013_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(
    mut v_type_1014_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_1015_: *mut leanh::LeanObject,
    mut v_k_1016_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1017_: u8,
    mut v_whnfType_1018_: u8,
    mut v___y_1019_: *mut leanh::LeanObject,
    mut v___y_1020_: *mut leanh::LeanObject,
    mut v___y_1021_: *mut leanh::LeanObject,
    mut v___y_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1033_: u8 = 0;
    let mut v_a_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1024_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_1024_, 0, v_k_1016_);
                v___x_1025_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    leanh::lean_box(0),
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
                if leanh::lean_obj_tag(v___x_1025_) == 0 {
                    v_a_1026_ = leanh::lean_ctor_get(v___x_1025_, 0);
                    v_isSharedCheck_1033_ = (!leanh::lean_is_exclusive(v___x_1025_)) as u8;
                    if v_isSharedCheck_1033_ == 0 {
                        v___x_1028_ = v___x_1025_;
                        v_isShared_1029_ = v_isSharedCheck_1033_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1026_);
                        leanh::lean_dec(v___x_1025_);
                        v___x_1028_ = leanh::lean_box(0);
                        v_isShared_1029_ = v_isSharedCheck_1033_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1034_ = leanh::lean_ctor_get(v___x_1025_, 0);
                    v_isSharedCheck_1041_ = (!leanh::lean_is_exclusive(v___x_1025_)) as u8;
                    if v_isSharedCheck_1041_ == 0 {
                        v___x_1036_ = v___x_1025_;
                        v_isShared_1037_ = v_isSharedCheck_1041_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1034_);
                        leanh::lean_dec(v___x_1025_);
                        v___x_1036_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
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
                    v_reuseFailAlloc_1040_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
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
    mut v_type_1042_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_1043_: *mut leanh::LeanObject,
    mut v_k_1044_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1045_: *mut leanh::LeanObject,
    mut v_whnfType_1046_: *mut leanh::LeanObject,
    mut v___y_1047_: *mut leanh::LeanObject,
    mut v___y_1048_: *mut leanh::LeanObject,
    mut v___y_1049_: *mut leanh::LeanObject,
    mut v___y_1050_: *mut leanh::LeanObject,
    mut v___y_1051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1052_: u8 = 0;
    let mut v_whnfType_boxed_1053_: u8 = 0;
    let mut v_res_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1052_ = (leanh::lean_unbox(v_cleanupAnnotations_1045_) as u8);
    v_whnfType_boxed_1053_ = (leanh::lean_unbox(v_whnfType_1046_) as u8);
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
    leanh::lean_dec(v___y_1050_);
    leanh::lean_dec_ref(v___y_1049_);
    leanh::lean_dec(v___y_1048_);
    leanh::lean_dec_ref(v___y_1047_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(
    mut v_00_u03b1_1055_: *mut leanh::LeanObject,
    mut v_type_1056_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_1057_: *mut leanh::LeanObject,
    mut v_k_1058_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1059_: u8,
    mut v_whnfType_1060_: u8,
    mut v___y_1061_: *mut leanh::LeanObject,
    mut v___y_1062_: *mut leanh::LeanObject,
    mut v___y_1063_: *mut leanh::LeanObject,
    mut v___y_1064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1067_: *mut leanh::LeanObject,
    mut v_type_1068_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_1069_: *mut leanh::LeanObject,
    mut v_k_1070_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1071_: *mut leanh::LeanObject,
    mut v_whnfType_1072_: *mut leanh::LeanObject,
    mut v___y_1073_: *mut leanh::LeanObject,
    mut v___y_1074_: *mut leanh::LeanObject,
    mut v___y_1075_: *mut leanh::LeanObject,
    mut v___y_1076_: *mut leanh::LeanObject,
    mut v___y_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1078_: u8 = 0;
    let mut v_whnfType_boxed_1079_: u8 = 0;
    let mut v_res_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1078_ = (leanh::lean_unbox(v_cleanupAnnotations_1071_) as u8);
    v_whnfType_boxed_1079_ = (leanh::lean_unbox(v_whnfType_1072_) as u8);
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
    leanh::lean_dec(v___y_1076_);
    leanh::lean_dec_ref(v___y_1075_);
    leanh::lean_dec(v___y_1074_);
    leanh::lean_dec_ref(v___y_1073_);
    return v_res_1080_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(
    mut v___x_1081_: *mut leanh::LeanObject,
    mut v_a_1082_: *mut leanh::LeanObject,
    mut v_sz_1083_: usize,
    mut v_i_1084_: usize,
    mut v_bs_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1086_: u8 = 0;
    let mut v_v_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1091_: usize = 0;
    let mut v___x_1092_: usize = 0;
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1086_ = lean_usize_dec_lt(v_i_1084_, v_sz_1083_);
                if v___x_1086_ == 0 {
                    leanh::lean_dec_ref(v___x_1081_);
                    return v_bs_1085_;
                } else {
                    v_v_1087_ = lean_array_uget(v_bs_1085_, v_i_1084_);
                    v___x_1088_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1089_ = lean_array_uset(v_bs_1085_, v_i_1084_, v___x_1088_);
                    leanh::lean_inc_ref(v___x_1081_);
                    v___x_1090_ = l_Lean_Meta_occursOrInType(v___x_1081_, v_v_1087_, v_a_1082_);
                    v___x_1091_ = 1usize;
                    v___x_1092_ = lean_usize_add(v_i_1084_, v___x_1091_);
                    v___x_1093_ = leanh::lean_box((v___x_1090_) as usize);
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
    mut v___x_1096_: *mut leanh::LeanObject,
    mut v_a_1097_: *mut leanh::LeanObject,
    mut v_sz_1098_: *mut leanh::LeanObject,
    mut v_i_1099_: *mut leanh::LeanObject,
    mut v_bs_1100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1101_: usize = 0;
    let mut v_i_boxed_1102_: usize = 0;
    let mut v_res_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1101_ = leanh::lean_unbox_usize(v_sz_1098_);
    leanh::lean_dec(v_sz_1098_);
    v_i_boxed_1102_ = leanh::lean_unbox_usize(v_i_1099_);
    leanh::lean_dec(v_i_1099_);
    v_res_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v___x_1096_, v_a_1097_, v_sz_boxed_1101_, v_i_boxed_1102_, v_bs_1100_);
    leanh::lean_dec_ref(v_a_1097_);
    return v_res_1103_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask___lam__0(
    mut v_ys_1104_: *mut leanh::LeanObject,
    mut v_ctorRet_1105_: *mut leanh::LeanObject,
    mut v___y_1106_: *mut leanh::LeanObject,
    mut v___y_1107_: *mut leanh::LeanObject,
    mut v___y_1108_: *mut leanh::LeanObject,
    mut v___y_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v_lctx_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1119_: usize = 0;
    let mut v___x_1120_: usize = 0;
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut v_a_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1129_: u8 = 0;
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1133_: u8 = 0;
    let mut v_a_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1137_: u8 = 0;
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1109_);
                leanh::lean_inc_ref(v___y_1108_);
                leanh::lean_inc(v___y_1107_);
                leanh::lean_inc_ref(v___y_1106_);
                v___x_1111_ = lean_whnf(
                    v_ctorRet_1105_,
                    v___y_1106_,
                    v___y_1107_,
                    v___y_1108_,
                    v___y_1109_,
                );
                if leanh::lean_obj_tag(v___x_1111_) == 0 {
                    v_a_1112_ = leanh::lean_ctor_get(v___x_1111_, 0);
                    leanh::lean_inc(v_a_1112_);
                    leanh::lean_dec_ref_known(v___x_1111_, 1);
                    v___x_1113_ = l_Lean_Core_betaReduce(v_a_1112_, v___y_1108_, v___y_1109_);
                    if leanh::lean_obj_tag(v___x_1113_) == 0 {
                        v_a_1114_ = leanh::lean_ctor_get(v___x_1113_, 0);
                        v_isSharedCheck_1125_ =
                            (!leanh::lean_is_exclusive(v___x_1113_)) as u8;
                        if v_isSharedCheck_1125_ == 0 {
                            v___x_1116_ = v___x_1113_;
                            v_isShared_1117_ = v_isSharedCheck_1125_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1114_);
                            leanh::lean_dec(v___x_1113_);
                            v___x_1116_ = leanh::lean_box(0);
                            v_isShared_1117_ = v_isSharedCheck_1125_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_ys_1104_);
                        v_a_1126_ = leanh::lean_ctor_get(v___x_1113_, 0);
                        v_isSharedCheck_1133_ =
                            (!leanh::lean_is_exclusive(v___x_1113_)) as u8;
                        if v_isSharedCheck_1133_ == 0 {
                            v___x_1128_ = v___x_1113_;
                            v_isShared_1129_ = v_isSharedCheck_1133_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1126_);
                            leanh::lean_dec(v___x_1113_);
                            v___x_1128_ = leanh::lean_box(0);
                            v_isShared_1129_ = v_isSharedCheck_1133_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_ys_1104_);
                    v_a_1134_ = leanh::lean_ctor_get(v___x_1111_, 0);
                    v_isSharedCheck_1141_ = (!leanh::lean_is_exclusive(v___x_1111_)) as u8;
                    if v_isSharedCheck_1141_ == 0 {
                        v___x_1136_ = v___x_1111_;
                        v_isShared_1137_ = v_isSharedCheck_1141_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1134_);
                        leanh::lean_dec(v___x_1111_);
                        v___x_1136_ = leanh::lean_box(0);
                        v_isShared_1137_ = v_isSharedCheck_1141_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_lctx_1118_ = leanh::lean_ctor_get(v___y_1106_, 2);
                v_sz_1119_ = lean_array_size(v_ys_1104_);
                v___x_1120_ = 0usize;
                leanh::lean_inc_ref(v_lctx_1118_);
                v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v_lctx_1118_, v_a_1114_, v_sz_1119_, v___x_1120_, v_ys_1104_);
                leanh::lean_dec(v_a_1114_);
                if v_isShared_1117_ == 0 {
                    leanh::lean_ctor_set(v___x_1116_, 0, v___x_1121_);
                    v___x_1123_ = v___x_1116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
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
                    v_reuseFailAlloc_1132_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
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
                    v_reuseFailAlloc_1140_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
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
    mut v_ys_1142_: *mut leanh::LeanObject,
    mut v_ctorRet_1143_: *mut leanh::LeanObject,
    mut v___y_1144_: *mut leanh::LeanObject,
    mut v___y_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
    mut v___y_1147_: *mut leanh::LeanObject,
    mut v___y_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Lean_Meta_occursInCtorTypeMask___lam__0(
        v_ys_1142_,
        v_ctorRet_1143_,
        v___y_1144_,
        v___y_1145_,
        v___y_1146_,
        v___y_1147_,
    );
    leanh::lean_dec(v___y_1147_);
    leanh::lean_dec_ref(v___y_1146_);
    leanh::lean_dec(v___y_1145_);
    leanh::lean_dec_ref(v___y_1144_);
    return v_res_1149_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask___lam__1(
    mut v_numFields_1150_: *mut leanh::LeanObject,
    mut v___f_1151_: *mut leanh::LeanObject,
    mut v_x_1152_: *mut leanh::LeanObject,
    mut v_ctorRet_1153_: *mut leanh::LeanObject,
    mut v___y_1154_: *mut leanh::LeanObject,
    mut v___y_1155_: *mut leanh::LeanObject,
    mut v___y_1156_: *mut leanh::LeanObject,
    mut v___y_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1159_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1159_, 0, v_numFields_1150_);
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
    mut v_numFields_1162_: *mut leanh::LeanObject,
    mut v___f_1163_: *mut leanh::LeanObject,
    mut v_x_1164_: *mut leanh::LeanObject,
    mut v_ctorRet_1165_: *mut leanh::LeanObject,
    mut v___y_1166_: *mut leanh::LeanObject,
    mut v___y_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
    mut v___y_1169_: *mut leanh::LeanObject,
    mut v___y_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1169_);
    leanh::lean_dec_ref(v___y_1168_);
    leanh::lean_dec(v___y_1167_);
    leanh::lean_dec_ref(v___y_1166_);
    leanh::lean_dec_ref(v_x_1164_);
    return v_res_1171_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_1172_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(
    mut v_msg_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
    mut v___y_1179_: *mut leanh::LeanObject,
    mut v___y_1180_: *mut leanh::LeanObject,
    mut v___y_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1188_: u8 = 0;
    let mut v_toFunctor_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1195_: u8 = 0;
    let mut v___f_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1212_: u8 = 0;
    let mut v_toFunctor_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1219_: u8 = 0;
    let mut v___f_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065__overap_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut v_unused_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_unused_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v_unused_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1246_: u8 = 0;
    let mut v_unused_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1183_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0);
                v___x_1184_ = l_StateRefT_x27_instMonad___redArg(v___x_1183_);
                v_toApplicative_1185_ = leanh::lean_ctor_get(v___x_1184_, 0);
                v_isSharedCheck_1246_ = (!leanh::lean_is_exclusive(v___x_1184_)) as u8;
                if v_isSharedCheck_1246_ == 0 {
                    v_unused_1247_ = leanh::lean_ctor_get(v___x_1184_, 1);
                    leanh::lean_dec(v_unused_1247_);
                    v___x_1187_ = v___x_1184_;
                    v_isShared_1188_ = v_isSharedCheck_1246_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1185_);
                    leanh::lean_dec(v___x_1184_);
                    v___x_1187_ = leanh::lean_box(0);
                    v_isShared_1188_ = v_isSharedCheck_1246_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1189_ = leanh::lean_ctor_get(v_toApplicative_1185_, 0);
                v_toSeq_1190_ = leanh::lean_ctor_get(v_toApplicative_1185_, 2);
                v_toSeqLeft_1191_ = leanh::lean_ctor_get(v_toApplicative_1185_, 3);
                v_toSeqRight_1192_ = leanh::lean_ctor_get(v_toApplicative_1185_, 4);
                v_isSharedCheck_1244_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1185_)) as u8;
                if v_isSharedCheck_1244_ == 0 {
                    v_unused_1245_ = leanh::lean_ctor_get(v_toApplicative_1185_, 1);
                    leanh::lean_dec(v_unused_1245_);
                    v___x_1194_ = v_toApplicative_1185_;
                    v_isShared_1195_ = v_isSharedCheck_1244_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1192_);
                    leanh::lean_inc(v_toSeqLeft_1191_);
                    leanh::lean_inc(v_toSeq_1190_);
                    leanh::lean_inc(v_toFunctor_1189_);
                    leanh::lean_dec(v_toApplicative_1185_);
                    v___x_1194_ = leanh::lean_box(0);
                    v_isShared_1195_ = v_isSharedCheck_1244_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1196_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1;
                v___f_1197_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2;
                leanh::lean_inc_ref(v_toFunctor_1189_);
                v___f_1198_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1198_, 0, v_toFunctor_1189_);
                v___f_1199_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1199_, 0, v_toFunctor_1189_);
                v___x_1200_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1200_, 0, v___f_1198_);
                leanh::lean_ctor_set(v___x_1200_, 1, v___f_1199_);
                v___f_1201_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1201_, 0, v_toSeqRight_1192_);
                v___f_1202_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1202_, 0, v_toSeqLeft_1191_);
                v___f_1203_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1203_, 0, v_toSeq_1190_);
                if v_isShared_1195_ == 0 {
                    leanh::lean_ctor_set(v___x_1194_, 4, v___f_1201_);
                    leanh::lean_ctor_set(v___x_1194_, 3, v___f_1202_);
                    leanh::lean_ctor_set(v___x_1194_, 2, v___f_1203_);
                    leanh::lean_ctor_set(v___x_1194_, 1, v___f_1196_);
                    leanh::lean_ctor_set(v___x_1194_, 0, v___x_1200_);
                    v___x_1205_ = v___x_1194_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___f_1196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 2, v___f_1203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 3, v___f_1202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 4, v___f_1201_);
                    v___x_1205_ = v_reuseFailAlloc_1243_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1188_ == 0 {
                    leanh::lean_ctor_set(v___x_1187_, 1, v___f_1197_);
                    leanh::lean_ctor_set(v___x_1187_, 0, v___x_1205_);
                    v___x_1207_ = v___x_1187_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1242_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___f_1197_);
                    v___x_1207_ = v_reuseFailAlloc_1242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1208_ = l_StateRefT_x27_instMonad___redArg(v___x_1207_);
                v_toApplicative_1209_ = leanh::lean_ctor_get(v___x_1208_, 0);
                v_isSharedCheck_1240_ = (!leanh::lean_is_exclusive(v___x_1208_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v_unused_1241_ = leanh::lean_ctor_get(v___x_1208_, 1);
                    leanh::lean_dec(v_unused_1241_);
                    v___x_1211_ = v___x_1208_;
                    v_isShared_1212_ = v_isSharedCheck_1240_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1209_);
                    leanh::lean_dec(v___x_1208_);
                    v___x_1211_ = leanh::lean_box(0);
                    v_isShared_1212_ = v_isSharedCheck_1240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1213_ = leanh::lean_ctor_get(v_toApplicative_1209_, 0);
                v_toSeq_1214_ = leanh::lean_ctor_get(v_toApplicative_1209_, 2);
                v_toSeqLeft_1215_ = leanh::lean_ctor_get(v_toApplicative_1209_, 3);
                v_toSeqRight_1216_ = leanh::lean_ctor_get(v_toApplicative_1209_, 4);
                v_isSharedCheck_1238_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1209_)) as u8;
                if v_isSharedCheck_1238_ == 0 {
                    v_unused_1239_ = leanh::lean_ctor_get(v_toApplicative_1209_, 1);
                    leanh::lean_dec(v_unused_1239_);
                    v___x_1218_ = v_toApplicative_1209_;
                    v_isShared_1219_ = v_isSharedCheck_1238_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1216_);
                    leanh::lean_inc(v_toSeqLeft_1215_);
                    leanh::lean_inc(v_toSeq_1214_);
                    leanh::lean_inc(v_toFunctor_1213_);
                    leanh::lean_dec(v_toApplicative_1209_);
                    v___x_1218_ = leanh::lean_box(0);
                    v_isShared_1219_ = v_isSharedCheck_1238_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1220_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3;
                v___f_1221_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4;
                leanh::lean_inc_ref(v_toFunctor_1213_);
                v___f_1222_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1222_, 0, v_toFunctor_1213_);
                v___f_1223_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1223_, 0, v_toFunctor_1213_);
                v___x_1224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1224_, 0, v___f_1222_);
                leanh::lean_ctor_set(v___x_1224_, 1, v___f_1223_);
                v___f_1225_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1225_, 0, v_toSeqRight_1216_);
                v___f_1226_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1226_, 0, v_toSeqLeft_1215_);
                v___f_1227_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1227_, 0, v_toSeq_1214_);
                if v_isShared_1219_ == 0 {
                    leanh::lean_ctor_set(v___x_1218_, 4, v___f_1225_);
                    leanh::lean_ctor_set(v___x_1218_, 3, v___f_1226_);
                    leanh::lean_ctor_set(v___x_1218_, 2, v___f_1227_);
                    leanh::lean_ctor_set(v___x_1218_, 1, v___f_1220_);
                    leanh::lean_ctor_set(v___x_1218_, 0, v___x_1224_);
                    v___x_1229_ = v___x_1218_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1237_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___f_1220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 2, v___f_1227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 3, v___f_1226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 4, v___f_1225_);
                    v___x_1229_ = v_reuseFailAlloc_1237_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1212_ == 0 {
                    leanh::lean_ctor_set(v___x_1211_, 1, v___f_1221_);
                    leanh::lean_ctor_set(v___x_1211_, 0, v___x_1229_);
                    v___x_1231_ = v___x_1211_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___f_1221_);
                    v___x_1231_ = v_reuseFailAlloc_1236_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1232_ = leanh::lean_box(0);
                v___x_1233_ = l_instInhabitedOfMonad___redArg(v___x_1231_, v___x_1232_);
                v___x_2065__overap_1234_ = lean_panic_fn_borrowed(v___x_1233_, v_msg_1177_);
                leanh::lean_dec(v___x_1233_);
                leanh::lean_inc(v___y_1181_);
                leanh::lean_inc_ref(v___y_1180_);
                leanh::lean_inc(v___y_1179_);
                leanh::lean_inc_ref(v___y_1178_);
                v___x_1235_ = leanh::lean_apply_5(
                    v___x_2065__overap_1234_,
                    v___y_1178_,
                    v___y_1179_,
                    v___y_1180_,
                    v___y_1181_,
                    leanh::lean_box(0),
                );
                return v___x_1235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___boxed(
    mut v_msg_1248_: *mut leanh::LeanObject,
    mut v___y_1249_: *mut leanh::LeanObject,
    mut v___y_1250_: *mut leanh::LeanObject,
    mut v___y_1251_: *mut leanh::LeanObject,
    mut v___y_1252_: *mut leanh::LeanObject,
    mut v___y_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v_msg_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
    leanh::lean_dec(v___y_1252_);
    leanh::lean_dec_ref(v___y_1251_);
    leanh::lean_dec(v___y_1250_);
    leanh::lean_dec_ref(v___y_1249_);
    return v_res_1254_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(
    mut v_msgData_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = lean_st_ref_get(v___y_1259_);
    v_env_1262_ = leanh::lean_ctor_get(v___x_1261_, 0);
    leanh::lean_inc_ref(v_env_1262_);
    leanh::lean_dec(v___x_1261_);
    v___x_1263_ = lean_st_ref_get(v___y_1257_);
    v_mctx_1264_ = leanh::lean_ctor_get(v___x_1263_, 0);
    leanh::lean_inc_ref(v_mctx_1264_);
    leanh::lean_dec(v___x_1263_);
    v_lctx_1265_ = leanh::lean_ctor_get(v___y_1256_, 2);
    v_options_1266_ = leanh::lean_ctor_get(v___y_1258_, 2);
    leanh::lean_inc_ref(v_options_1266_);
    leanh::lean_inc_ref(v_lctx_1265_);
    v___x_1267_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1267_, 0, v_env_1262_);
    leanh::lean_ctor_set(v___x_1267_, 1, v_mctx_1264_);
    leanh::lean_ctor_set(v___x_1267_, 2, v_lctx_1265_);
    leanh::lean_ctor_set(v___x_1267_, 3, v_options_1266_);
    v___x_1268_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    leanh::lean_ctor_set(v___x_1268_, 1, v_msgData_1255_);
    v___x_1269_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1269_, 0, v___x_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_1270_: *mut leanh::LeanObject,
    mut v___y_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msgData_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
    leanh::lean_dec(v___y_1274_);
    leanh::lean_dec_ref(v___y_1273_);
    leanh::lean_dec(v___y_1272_);
    leanh::lean_dec_ref(v___y_1271_);
    return v_res_1276_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(
    mut v_msg_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
    mut v___y_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1293_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1283_ = leanh::lean_ctor_get(v___y_1280_, 5);
                v___x_1284_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msg_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
                v_a_1285_ = leanh::lean_ctor_get(v___x_1284_, 0);
                v_isSharedCheck_1293_ = (!leanh::lean_is_exclusive(v___x_1284_)) as u8;
                if v_isSharedCheck_1293_ == 0 {
                    v___x_1287_ = v___x_1284_;
                    v_isShared_1288_ = v_isSharedCheck_1293_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1285_);
                    leanh::lean_dec(v___x_1284_);
                    v___x_1287_ = leanh::lean_box(0);
                    v_isShared_1288_ = v_isSharedCheck_1293_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1283_);
                v___x_1289_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1289_, 0, v_ref_1283_);
                leanh::lean_ctor_set(v___x_1289_, 1, v_a_1285_);
                if v_isShared_1288_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1287_, 1);
                    leanh::lean_ctor_set(v___x_1287_, 0, v___x_1289_);
                    v___x_1291_ = v___x_1287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1292_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
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
    mut v_msg_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
    mut v___y_1298_: *mut leanh::LeanObject,
    mut v___y_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
    leanh::lean_dec(v___y_1298_);
    leanh::lean_dec_ref(v___y_1297_);
    leanh::lean_dec(v___y_1296_);
    leanh::lean_dec_ref(v___y_1295_);
    return v_res_1300_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0;
    v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2;
    v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
    return v___x_1306_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1310_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6;
    v___x_1311_ = leanh::lean_unsigned_to_nat(11);
    v___x_1312_ = leanh::lean_unsigned_to_nat(122);
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
    mut v_constName_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
    mut v___y_1318_: *mut leanh::LeanObject,
    mut v___y_1319_: *mut leanh::LeanObject,
    mut v___y_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: u8 = 0;
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1335_: u8 = 0;
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v_val_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_a_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1330_ = lean_st_ref_get(v___y_1320_);
                v_env_1331_ = leanh::lean_ctor_get(v___x_1330_, 0);
                leanh::lean_inc_ref(v_env_1331_);
                leanh::lean_dec(v___x_1330_);
                v___x_1332_ = 0;
                leanh::lean_inc(v_constName_1316_);
                v___x_1333_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1331_, v_constName_1316_, v___x_1332_);
                if leanh::lean_obj_tag(v___x_1333_) == 1 {
                    v_val_1334_ = leanh::lean_ctor_get(v___x_1333_, 0);
                    leanh::lean_inc(v_val_1334_);
                    leanh::lean_dec_ref_known(v___x_1333_, 1);
                    v_kind_1335_ = leanh::lean_ctor_get_uint8(
                        v_val_1334_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_1335_ == 6 {
                        v___x_1336_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1334_);
                        if leanh::lean_obj_tag(v___x_1336_) == 6 {
                            leanh::lean_dec(v_constName_1316_);
                            v_val_1337_ = leanh::lean_ctor_get(v___x_1336_, 0);
                            v_isSharedCheck_1344_ =
                                (!leanh::lean_is_exclusive(v___x_1336_)) as u8;
                            if v_isSharedCheck_1344_ == 0 {
                                v___x_1339_ = v___x_1336_;
                                v_isShared_1340_ = v_isSharedCheck_1344_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_1337_);
                                leanh::lean_dec(v___x_1336_);
                                v___x_1339_ = leanh::lean_box(0);
                                v_isShared_1340_ = v_isSharedCheck_1344_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1336_);
                            v___x_1345_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7);
                            v___x_1346_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v___x_1345_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
                            if leanh::lean_obj_tag(v___x_1346_) == 0 {
                                v_a_1347_ = leanh::lean_ctor_get(v___x_1346_, 0);
                                v_isSharedCheck_1355_ =
                                    (!leanh::lean_is_exclusive(v___x_1346_)) as u8;
                                if v_isSharedCheck_1355_ == 0 {
                                    v___x_1349_ = v___x_1346_;
                                    v_isShared_1350_ = v_isSharedCheck_1355_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1347_);
                                    leanh::lean_dec(v___x_1346_);
                                    v___x_1349_ = leanh::lean_box(0);
                                    v_isShared_1350_ = v_isSharedCheck_1355_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_constName_1316_);
                                v_a_1356_ = leanh::lean_ctor_get(v___x_1346_, 0);
                                v_isSharedCheck_1363_ =
                                    (!leanh::lean_is_exclusive(v___x_1346_)) as u8;
                                if v_isSharedCheck_1363_ == 0 {
                                    v___x_1358_ = v___x_1346_;
                                    v_isShared_1359_ = v_isSharedCheck_1363_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1356_);
                                    leanh::lean_dec(v___x_1346_);
                                    v___x_1358_ = leanh::lean_box(0);
                                    v_isShared_1359_ = v_isSharedCheck_1363_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_1334_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1333_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1323_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
                v___x_1324_ = 0;
                v___x_1325_ = l_Lean_MessageData_ofConstName(v_constName_1316_, v___x_1324_);
                v___x_1326_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1326_, 0, v___x_1323_);
                leanh::lean_ctor_set(v___x_1326_, 1, v___x_1325_);
                v___x_1327_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3);
                v___x_1328_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1328_, 0, v___x_1326_);
                leanh::lean_ctor_set(v___x_1328_, 1, v___x_1327_);
                v___x_1329_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_1328_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
                return v___x_1329_;
            }
            2 => {
                if v_isShared_1340_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1339_, 0);
                    v___x_1342_ = v___x_1339_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1343_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_val_1337_);
                    v___x_1342_ = v_reuseFailAlloc_1343_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1342_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_1347_) == 0 {
                    leanh::lean_del_object(v___x_1349_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_constName_1316_);
                    v_val_1351_ = leanh::lean_ctor_get(v_a_1347_, 0);
                    leanh::lean_inc(v_val_1351_);
                    leanh::lean_dec_ref_known(v_a_1347_, 1);
                    if v_isShared_1350_ == 0 {
                        leanh::lean_ctor_set(v___x_1349_, 0, v_val_1351_);
                        v___x_1353_ = v___x_1349_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1354_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_val_1351_);
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
                    v_reuseFailAlloc_1362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
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
    mut v_constName_1364_: *mut leanh::LeanObject,
    mut v___y_1365_: *mut leanh::LeanObject,
    mut v___y_1366_: *mut leanh::LeanObject,
    mut v___y_1367_: *mut leanh::LeanObject,
    mut v___y_1368_: *mut leanh::LeanObject,
    mut v___y_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1370_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(
        v_constName_1364_,
        v___y_1365_,
        v___y_1366_,
        v___y_1367_,
        v___y_1368_,
    );
    leanh::lean_dec(v___y_1368_);
    leanh::lean_dec_ref(v___y_1367_);
    leanh::lean_dec(v___y_1366_);
    leanh::lean_dec_ref(v___y_1365_);
    return v_res_1370_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask(
    mut v_ctorName_1372_: *mut leanh::LeanObject,
    mut v_a_1373_: *mut leanh::LeanObject,
    mut v_a_1374_: *mut leanh::LeanObject,
    mut v_a_1375_: *mut leanh::LeanObject,
    mut v_a_1376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1392_: u8 = 0;
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1378_) == 0 {
                    v_a_1379_ = leanh::lean_ctor_get(v___x_1378_, 0);
                    leanh::lean_inc(v_a_1379_);
                    leanh::lean_dec_ref_known(v___x_1378_, 1);
                    v_toConstantVal_1380_ = leanh::lean_ctor_get(v_a_1379_, 0);
                    leanh::lean_inc_ref(v_toConstantVal_1380_);
                    v_numParams_1381_ = leanh::lean_ctor_get(v_a_1379_, 3);
                    leanh::lean_inc(v_numParams_1381_);
                    v_numFields_1382_ = leanh::lean_ctor_get(v_a_1379_, 4);
                    leanh::lean_inc(v_numFields_1382_);
                    leanh::lean_dec(v_a_1379_);
                    v_type_1383_ = leanh::lean_ctor_get(v_toConstantVal_1380_, 2);
                    leanh::lean_inc_ref(v_type_1383_);
                    leanh::lean_dec_ref(v_toConstantVal_1380_);
                    v___f_1384_ = l_Lean_Meta_occursInCtorTypeMask___closed__0;
                    v___f_1385_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1385_, 0, v_numFields_1382_);
                    leanh::lean_closure_set(v___f_1385_, 1, v___f_1384_);
                    v___x_1386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1386_, 0, v_numParams_1381_);
                    v___x_1387_ = 0;
                    v___x_1388_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_1383_, v___x_1386_, v___f_1385_, v___x_1387_, v___x_1387_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
                    return v___x_1388_;
                } else {
                    v_a_1389_ = leanh::lean_ctor_get(v___x_1378_, 0);
                    v_isSharedCheck_1396_ = (!leanh::lean_is_exclusive(v___x_1378_)) as u8;
                    if v_isSharedCheck_1396_ == 0 {
                        v___x_1391_ = v___x_1378_;
                        v_isShared_1392_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1389_);
                        leanh::lean_dec(v___x_1378_);
                        v___x_1391_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
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
    mut v_ctorName_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
    mut v_a_1401_: *mut leanh::LeanObject,
    mut v_a_1402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lean_Meta_occursInCtorTypeMask(
        v_ctorName_1397_,
        v_a_1398_,
        v_a_1399_,
        v_a_1400_,
        v_a_1401_,
    );
    leanh::lean_dec(v_a_1401_);
    leanh::lean_dec_ref(v_a_1400_);
    leanh::lean_dec(v_a_1399_);
    leanh::lean_dec_ref(v_a_1398_);
    return v_res_1403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(
    mut v_00_u03b1_1404_: *mut leanh::LeanObject,
    mut v_msg_1405_: *mut leanh::LeanObject,
    mut v___y_1406_: *mut leanh::LeanObject,
    mut v___y_1407_: *mut leanh::LeanObject,
    mut v___y_1408_: *mut leanh::LeanObject,
    mut v___y_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
    return v___x_1411_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___boxed(
    mut v_00_u03b1_1412_: *mut leanh::LeanObject,
    mut v_msg_1413_: *mut leanh::LeanObject,
    mut v___y_1414_: *mut leanh::LeanObject,
    mut v___y_1415_: *mut leanh::LeanObject,
    mut v___y_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1419_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(v_00_u03b1_1412_, v_msg_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
    leanh::lean_dec(v___y_1417_);
    leanh::lean_dec_ref(v___y_1416_);
    leanh::lean_dec(v___y_1415_);
    leanh::lean_dec_ref(v___y_1414_);
    return v_res_1419_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(
    mut v_msg_1421_: *mut leanh::LeanObject,
    mut v___y_1422_: *mut leanh::LeanObject,
    mut v___y_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
    mut v___y_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685__overap_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1427_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0;
    v___x_685__overap_1428_ = lean_panic_fn_borrowed(v___f_1427_, v_msg_1421_);
    leanh::lean_inc(v___y_1425_);
    leanh::lean_inc_ref(v___y_1424_);
    leanh::lean_inc(v___y_1423_);
    leanh::lean_inc_ref(v___y_1422_);
    v___x_1429_ = leanh::lean_apply_5(
        v___x_685__overap_1428_,
        v___y_1422_,
        v___y_1423_,
        v___y_1424_,
        v___y_1425_,
        leanh::lean_box(0),
    );
    return v___x_1429_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___boxed(
    mut v_msg_1430_: *mut leanh::LeanObject,
    mut v___y_1431_: *mut leanh::LeanObject,
    mut v___y_1432_: *mut leanh::LeanObject,
    mut v___y_1433_: *mut leanh::LeanObject,
    mut v___y_1434_: *mut leanh::LeanObject,
    mut v___y_1435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1436_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
    leanh::lean_dec(v___y_1434_);
    leanh::lean_dec_ref(v___y_1433_);
    leanh::lean_dec(v___y_1432_);
    leanh::lean_dec_ref(v___y_1431_);
    return v_res_1436_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(
    mut v_00_u03b1_1437_: *mut leanh::LeanObject,
    mut v_msg_1438_: *mut leanh::LeanObject,
    mut v___y_1439_: *mut leanh::LeanObject,
    mut v___y_1440_: *mut leanh::LeanObject,
    mut v___y_1441_: *mut leanh::LeanObject,
    mut v___y_1442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1444_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
    return v___x_1444_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___boxed(
    mut v_00_u03b1_1445_: *mut leanh::LeanObject,
    mut v_msg_1446_: *mut leanh::LeanObject,
    mut v___y_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(v_00_u03b1_1445_, v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
    leanh::lean_dec(v___y_1450_);
    leanh::lean_dec_ref(v___y_1449_);
    leanh::lean_dec(v___y_1448_);
    leanh::lean_dec_ref(v___y_1447_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(
    mut v_k_1453_: *mut leanh::LeanObject,
    mut v_b_1454_: *mut leanh::LeanObject,
    mut v___y_1455_: *mut leanh::LeanObject,
    mut v___y_1456_: *mut leanh::LeanObject,
    mut v___y_1457_: *mut leanh::LeanObject,
    mut v___y_1458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1458_);
    leanh::lean_inc_ref(v___y_1457_);
    leanh::lean_inc(v___y_1456_);
    leanh::lean_inc_ref(v___y_1455_);
    v___x_1460_ = leanh::lean_apply_6(
        v_k_1453_,
        v_b_1454_,
        v___y_1455_,
        v___y_1456_,
        v___y_1457_,
        v___y_1458_,
        leanh::lean_box(0),
    );
    return v___x_1460_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed(
    mut v_k_1461_: *mut leanh::LeanObject,
    mut v_b_1462_: *mut leanh::LeanObject,
    mut v___y_1463_: *mut leanh::LeanObject,
    mut v___y_1464_: *mut leanh::LeanObject,
    mut v___y_1465_: *mut leanh::LeanObject,
    mut v___y_1466_: *mut leanh::LeanObject,
    mut v___y_1467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1468_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(v_k_1461_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
    leanh::lean_dec(v___y_1466_);
    leanh::lean_dec_ref(v___y_1465_);
    leanh::lean_dec(v___y_1464_);
    leanh::lean_dec_ref(v___y_1463_);
    return v_res_1468_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(
    mut v_name_1469_: *mut leanh::LeanObject,
    mut v_bi_1470_: u8,
    mut v_type_1471_: *mut leanh::LeanObject,
    mut v_k_1472_: *mut leanh::LeanObject,
    mut v_kind_1473_: u8,
    mut v___y_1474_: *mut leanh::LeanObject,
    mut v___y_1475_: *mut leanh::LeanObject,
    mut v___y_1476_: *mut leanh::LeanObject,
    mut v___y_1477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_a_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1479_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_1479_, 0, v_k_1472_);
                v___x_1480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
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
                if leanh::lean_obj_tag(v___x_1480_) == 0 {
                    v_a_1481_ = leanh::lean_ctor_get(v___x_1480_, 0);
                    v_isSharedCheck_1488_ = (!leanh::lean_is_exclusive(v___x_1480_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1483_ = v___x_1480_;
                        v_isShared_1484_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1481_);
                        leanh::lean_dec(v___x_1480_);
                        v___x_1483_ = leanh::lean_box(0);
                        v_isShared_1484_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1489_ = leanh::lean_ctor_get(v___x_1480_, 0);
                    v_isSharedCheck_1496_ = (!leanh::lean_is_exclusive(v___x_1480_)) as u8;
                    if v_isSharedCheck_1496_ == 0 {
                        v___x_1491_ = v___x_1480_;
                        v_isShared_1492_ = v_isSharedCheck_1496_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1489_);
                        leanh::lean_dec(v___x_1480_);
                        v___x_1491_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1487_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
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
                    v_reuseFailAlloc_1495_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
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
    mut v_name_1497_: *mut leanh::LeanObject,
    mut v_bi_1498_: *mut leanh::LeanObject,
    mut v_type_1499_: *mut leanh::LeanObject,
    mut v_k_1500_: *mut leanh::LeanObject,
    mut v_kind_1501_: *mut leanh::LeanObject,
    mut v___y_1502_: *mut leanh::LeanObject,
    mut v___y_1503_: *mut leanh::LeanObject,
    mut v___y_1504_: *mut leanh::LeanObject,
    mut v___y_1505_: *mut leanh::LeanObject,
    mut v___y_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_1507_: u8 = 0;
    let mut v_kind_boxed_1508_: u8 = 0;
    let mut v_res_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1507_ = (leanh::lean_unbox(v_bi_1498_) as u8);
    v_kind_boxed_1508_ = (leanh::lean_unbox(v_kind_1501_) as u8);
    v_res_1509_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_1497_, v_bi_boxed_1507_, v_type_1499_, v_k_1500_, v_kind_boxed_1508_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
    leanh::lean_dec(v___y_1505_);
    leanh::lean_dec_ref(v___y_1504_);
    leanh::lean_dec(v___y_1503_);
    leanh::lean_dec_ref(v___y_1502_);
    return v_res_1509_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(
    mut v_name_1510_: *mut leanh::LeanObject,
    mut v_type_1511_: *mut leanh::LeanObject,
    mut v_k_1512_: *mut leanh::LeanObject,
    mut v___y_1513_: *mut leanh::LeanObject,
    mut v___y_1514_: *mut leanh::LeanObject,
    mut v___y_1515_: *mut leanh::LeanObject,
    mut v___y_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: u8 = 0;
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = 0;
    v___x_1519_ = 0;
    v___x_1520_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_1510_, v___x_1518_, v_type_1511_, v_k_1512_, v___x_1519_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
    return v___x_1520_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg___boxed(
    mut v_name_1521_: *mut leanh::LeanObject,
    mut v_type_1522_: *mut leanh::LeanObject,
    mut v_k_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
    mut v___y_1526_: *mut leanh::LeanObject,
    mut v___y_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_1521_, v_type_1522_, v_k_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
    leanh::lean_dec(v___y_1527_);
    leanh::lean_dec_ref(v___y_1526_);
    leanh::lean_dec(v___y_1525_);
    leanh::lean_dec_ref(v___y_1524_);
    return v_res_1529_;
}
pub unsafe fn _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2;
    v___x_1534_ = leanh::lean_unsigned_to_nat(8);
    v___x_1535_ = leanh::lean_unsigned_to_nat(91);
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
    mut v_zs2_1539_: *mut leanh::LeanObject,
    mut v_acc_1540_: *mut leanh::LeanObject,
    mut v_ctor_1541_: *mut leanh::LeanObject,
    mut v_k_1542_: *mut leanh::LeanObject,
    mut v_zs_1543_: *mut leanh::LeanObject,
    mut v_indices_1544_: *mut leanh::LeanObject,
    mut v_tail_1545_: *mut leanh::LeanObject,
    mut v_tail_1546_: *mut leanh::LeanObject,
    mut v_z_x27_1547_: *mut leanh::LeanObject,
    mut v___y_1548_: *mut leanh::LeanObject,
    mut v___y_1549_: *mut leanh::LeanObject,
    mut v___y_1550_: *mut leanh::LeanObject,
    mut v___y_1551_: *mut leanh::LeanObject,
    mut v___y_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1551_);
    leanh::lean_dec_ref(v___y_1550_);
    leanh::lean_dec(v___y_1549_);
    leanh::lean_dec_ref(v___y_1548_);
    return v_res_1553_;
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(
    mut v_ctor_1555_: *mut leanh::LeanObject,
    mut v_k_1556_: *mut leanh::LeanObject,
    mut v_zs_1557_: *mut leanh::LeanObject,
    mut v_indices_1558_: *mut leanh::LeanObject,
    mut v_zs2_1559_: *mut leanh::LeanObject,
    mut v_mask_1560_: *mut leanh::LeanObject,
    mut v_todo_1561_: *mut leanh::LeanObject,
    mut v_acc_1562_: *mut leanh::LeanObject,
    mut v_a_1563_: *mut leanh::LeanObject,
    mut v_a_1564_: *mut leanh::LeanObject,
    mut v_a_1565_: *mut leanh::LeanObject,
    mut v_a_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v_tail_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u8 = 0;
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1589_: u8 = 0;
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut v_a_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_mask_1560_) == 1 {
                    v_head_1568_ = leanh::lean_ctor_get(v_mask_1560_, 0);
                    v___x_1569_ = (leanh::lean_unbox(v_head_1568_) as u8);
                    if v___x_1569_ == 0 {
                        if leanh::lean_obj_tag(v_todo_1561_) == 1 {
                            v_tail_1570_ = leanh::lean_ctor_get(v_mask_1560_, 1);
                            leanh::lean_inc(v_tail_1570_);
                            leanh::lean_dec_ref_known(v_mask_1560_, 2);
                            v_tail_1571_ = leanh::lean_ctor_get(v_todo_1561_, 1);
                            leanh::lean_inc(v_tail_1571_);
                            leanh::lean_dec_ref_known(v_todo_1561_, 2);
                            leanh::lean_inc_ref(v_ctor_1555_);
                            v___x_1572_ = l_Lean_mkAppN(v_ctor_1555_, v_zs2_1559_);
                            leanh::lean_inc(v_a_1566_);
                            leanh::lean_inc_ref(v_a_1565_);
                            leanh::lean_inc(v_a_1564_);
                            leanh::lean_inc_ref(v_a_1563_);
                            v___x_1573_ = lean_infer_type(
                                v___x_1572_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                            );
                            if leanh::lean_obj_tag(v___x_1573_) == 0 {
                                v_a_1574_ = leanh::lean_ctor_get(v___x_1573_, 0);
                                leanh::lean_inc(v_a_1574_);
                                leanh::lean_dec_ref_known(v___x_1573_, 1);
                                v___x_1575_ = l_Lean_Meta_whnfForall(
                                    v_a_1574_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_,
                                );
                                if leanh::lean_obj_tag(v___x_1575_) == 0 {
                                    v_a_1576_ = leanh::lean_ctor_get(v___x_1575_, 0);
                                    leanh::lean_inc(v_a_1576_);
                                    leanh::lean_dec_ref_known(v___x_1575_, 1);
                                    v___x_1577_ = l_Lean_Expr_isForall(v_a_1576_);
                                    if v___x_1577_ == 0 {
                                        leanh::lean_dec(v_a_1576_);
                                        leanh::lean_dec(v_tail_1571_);
                                        leanh::lean_dec(v_tail_1570_);
                                        leanh::lean_dec_ref(v_acc_1562_);
                                        leanh::lean_dec_ref(v_zs2_1559_);
                                        leanh::lean_dec_ref(v_indices_1558_);
                                        leanh::lean_dec_ref(v_zs_1557_);
                                        leanh::lean_dec_ref(v_k_1556_);
                                        leanh::lean_dec_ref(v_ctor_1555_);
                                        v___x_1578_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once), _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3);
                                        v___x_1579_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v___x_1578_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
                                        return v___x_1579_;
                                    } else {
                                        v___f_1580_ = leanh::lean_alloc_closure(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 8);
                                        leanh::lean_closure_set(v___f_1580_, 0, v_zs2_1559_);
                                        leanh::lean_closure_set(v___f_1580_, 1, v_acc_1562_);
                                        leanh::lean_closure_set(
                                            v___f_1580_,
                                            2,
                                            v_ctor_1555_,
                                        );
                                        leanh::lean_closure_set(v___f_1580_, 3, v_k_1556_);
                                        leanh::lean_closure_set(v___f_1580_, 4, v_zs_1557_);
                                        leanh::lean_closure_set(
                                            v___f_1580_,
                                            5,
                                            v_indices_1558_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1580_,
                                            6,
                                            v_tail_1570_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1580_,
                                            7,
                                            v_tail_1571_,
                                        );
                                        v___x_1581_ = l_Lean_Expr_bindingName_x21(v_a_1576_);
                                        v___x_1582_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4;
                                        v___x_1583_ =
                                            lean_name_append_after(v___x_1581_, v___x_1582_);
                                        v___x_1584_ = l_Lean_Expr_bindingDomain_x21(v_a_1576_);
                                        leanh::lean_dec(v_a_1576_);
                                        v___x_1585_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v___x_1583_, v___x_1584_, v___f_1580_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
                                        return v___x_1585_;
                                    }
                                } else {
                                    leanh::lean_dec(v_tail_1571_);
                                    leanh::lean_dec(v_tail_1570_);
                                    leanh::lean_dec_ref(v_acc_1562_);
                                    leanh::lean_dec_ref(v_zs2_1559_);
                                    leanh::lean_dec_ref(v_indices_1558_);
                                    leanh::lean_dec_ref(v_zs_1557_);
                                    leanh::lean_dec_ref(v_k_1556_);
                                    leanh::lean_dec_ref(v_ctor_1555_);
                                    v_a_1586_ = leanh::lean_ctor_get(v___x_1575_, 0);
                                    v_isSharedCheck_1593_ =
                                        (!leanh::lean_is_exclusive(v___x_1575_)) as u8;
                                    if v_isSharedCheck_1593_ == 0 {
                                        v___x_1588_ = v___x_1575_;
                                        v_isShared_1589_ = v_isSharedCheck_1593_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1586_);
                                        leanh::lean_dec(v___x_1575_);
                                        v___x_1588_ = leanh::lean_box(0);
                                        v_isShared_1589_ = v_isSharedCheck_1593_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_tail_1571_);
                                leanh::lean_dec(v_tail_1570_);
                                leanh::lean_dec_ref(v_acc_1562_);
                                leanh::lean_dec_ref(v_zs2_1559_);
                                leanh::lean_dec_ref(v_indices_1558_);
                                leanh::lean_dec_ref(v_zs_1557_);
                                leanh::lean_dec_ref(v_k_1556_);
                                leanh::lean_dec_ref(v_ctor_1555_);
                                v_a_1594_ = leanh::lean_ctor_get(v___x_1573_, 0);
                                v_isSharedCheck_1601_ =
                                    (!leanh::lean_is_exclusive(v___x_1573_)) as u8;
                                if v_isSharedCheck_1601_ == 0 {
                                    v___x_1596_ = v___x_1573_;
                                    v_isShared_1597_ = v_isSharedCheck_1601_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1594_);
                                    leanh::lean_dec(v___x_1573_);
                                    v___x_1596_ = leanh::lean_box(0);
                                    v_isShared_1597_ = v_isSharedCheck_1601_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_mask_1560_, 2);
                            leanh::lean_dec(v_todo_1561_);
                            leanh::lean_dec_ref(v_ctor_1555_);
                            leanh::lean_inc(v_a_1566_);
                            leanh::lean_inc_ref(v_a_1565_);
                            leanh::lean_inc(v_a_1564_);
                            leanh::lean_inc_ref(v_a_1563_);
                            v___x_1602_ = leanh::lean_apply_9(
                                v_k_1556_,
                                v_acc_1562_,
                                v_indices_1558_,
                                v_zs_1557_,
                                v_zs2_1559_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                                leanh::lean_box(0),
                            );
                            return v___x_1602_;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_todo_1561_) == 1 {
                            v_tail_1603_ = leanh::lean_ctor_get(v_mask_1560_, 1);
                            leanh::lean_inc(v_tail_1603_);
                            leanh::lean_dec_ref_known(v_mask_1560_, 2);
                            v_head_1604_ = leanh::lean_ctor_get(v_todo_1561_, 0);
                            leanh::lean_inc(v_head_1604_);
                            v_tail_1605_ = leanh::lean_ctor_get(v_todo_1561_, 1);
                            leanh::lean_inc(v_tail_1605_);
                            leanh::lean_dec_ref_known(v_todo_1561_, 2);
                            v___x_1606_ = lean_array_push(v_zs2_1559_, v_head_1604_);
                            v_zs2_1559_ = v___x_1606_;
                            v_mask_1560_ = v_tail_1603_;
                            v_todo_1561_ = v_tail_1605_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_mask_1560_, 2);
                            leanh::lean_dec(v_todo_1561_);
                            leanh::lean_dec_ref(v_ctor_1555_);
                            leanh::lean_inc(v_a_1566_);
                            leanh::lean_inc_ref(v_a_1565_);
                            leanh::lean_inc(v_a_1564_);
                            leanh::lean_inc_ref(v_a_1563_);
                            v___x_1608_ = leanh::lean_apply_9(
                                v_k_1556_,
                                v_acc_1562_,
                                v_indices_1558_,
                                v_zs_1557_,
                                v_zs2_1559_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                                leanh::lean_box(0),
                            );
                            return v___x_1608_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_todo_1561_);
                    leanh::lean_dec(v_mask_1560_);
                    leanh::lean_dec_ref(v_ctor_1555_);
                    leanh::lean_inc(v_a_1566_);
                    leanh::lean_inc_ref(v_a_1565_);
                    leanh::lean_inc(v_a_1564_);
                    leanh::lean_inc_ref(v_a_1563_);
                    v___x_1609_ = leanh::lean_apply_9(
                        v_k_1556_,
                        v_acc_1562_,
                        v_indices_1558_,
                        v_zs_1557_,
                        v_zs2_1559_,
                        v_a_1563_,
                        v_a_1564_,
                        v_a_1565_,
                        v_a_1566_,
                        leanh::lean_box(0),
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
                    v_reuseFailAlloc_1592_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
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
                    v_reuseFailAlloc_1600_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
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
    mut v_zs2_1610_: *mut leanh::LeanObject,
    mut v_acc_1611_: *mut leanh::LeanObject,
    mut v_ctor_1612_: *mut leanh::LeanObject,
    mut v_k_1613_: *mut leanh::LeanObject,
    mut v_zs_1614_: *mut leanh::LeanObject,
    mut v_indices_1615_: *mut leanh::LeanObject,
    mut v_tail_1616_: *mut leanh::LeanObject,
    mut v_tail_1617_: *mut leanh::LeanObject,
    mut v_z_x27_1618_: *mut leanh::LeanObject,
    mut v___y_1619_: *mut leanh::LeanObject,
    mut v___y_1620_: *mut leanh::LeanObject,
    mut v___y_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_z_x27_1618_);
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
    mut v_ctor_1627_: *mut leanh::LeanObject,
    mut v_k_1628_: *mut leanh::LeanObject,
    mut v_zs_1629_: *mut leanh::LeanObject,
    mut v_indices_1630_: *mut leanh::LeanObject,
    mut v_zs2_1631_: *mut leanh::LeanObject,
    mut v_mask_1632_: *mut leanh::LeanObject,
    mut v_todo_1633_: *mut leanh::LeanObject,
    mut v_acc_1634_: *mut leanh::LeanObject,
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
    mut v_a_1638_: *mut leanh::LeanObject,
    mut v_a_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1638_);
    leanh::lean_dec_ref(v_a_1637_);
    leanh::lean_dec(v_a_1636_);
    leanh::lean_dec_ref(v_a_1635_);
    return v_res_1640_;
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(
    mut v_00_u03b1_1641_: *mut leanh::LeanObject,
    mut v_ctor_1642_: *mut leanh::LeanObject,
    mut v_k_1643_: *mut leanh::LeanObject,
    mut v_zs_1644_: *mut leanh::LeanObject,
    mut v_indices_1645_: *mut leanh::LeanObject,
    mut v_zs2_1646_: *mut leanh::LeanObject,
    mut v_mask_1647_: *mut leanh::LeanObject,
    mut v_todo_1648_: *mut leanh::LeanObject,
    mut v_acc_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
    mut v_a_1651_: *mut leanh::LeanObject,
    mut v_a_1652_: *mut leanh::LeanObject,
    mut v_a_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1656_: *mut leanh::LeanObject,
    mut v_ctor_1657_: *mut leanh::LeanObject,
    mut v_k_1658_: *mut leanh::LeanObject,
    mut v_zs_1659_: *mut leanh::LeanObject,
    mut v_indices_1660_: *mut leanh::LeanObject,
    mut v_zs2_1661_: *mut leanh::LeanObject,
    mut v_mask_1662_: *mut leanh::LeanObject,
    mut v_todo_1663_: *mut leanh::LeanObject,
    mut v_acc_1664_: *mut leanh::LeanObject,
    mut v_a_1665_: *mut leanh::LeanObject,
    mut v_a_1666_: *mut leanh::LeanObject,
    mut v_a_1667_: *mut leanh::LeanObject,
    mut v_a_1668_: *mut leanh::LeanObject,
    mut v_a_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1668_);
    leanh::lean_dec_ref(v_a_1667_);
    leanh::lean_dec(v_a_1666_);
    leanh::lean_dec_ref(v_a_1665_);
    return v_res_1670_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(
    mut v_00_u03b1_1671_: *mut leanh::LeanObject,
    mut v_name_1672_: *mut leanh::LeanObject,
    mut v_bi_1673_: u8,
    mut v_type_1674_: *mut leanh::LeanObject,
    mut v_k_1675_: *mut leanh::LeanObject,
    mut v_kind_1676_: u8,
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1682_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_1672_, v_bi_1673_, v_type_1674_, v_k_1675_, v_kind_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
    return v___x_1682_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___boxed(
    mut v_00_u03b1_1683_: *mut leanh::LeanObject,
    mut v_name_1684_: *mut leanh::LeanObject,
    mut v_bi_1685_: *mut leanh::LeanObject,
    mut v_type_1686_: *mut leanh::LeanObject,
    mut v_k_1687_: *mut leanh::LeanObject,
    mut v_kind_1688_: *mut leanh::LeanObject,
    mut v___y_1689_: *mut leanh::LeanObject,
    mut v___y_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_1694_: u8 = 0;
    let mut v_kind_boxed_1695_: u8 = 0;
    let mut v_res_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1694_ = (leanh::lean_unbox(v_bi_1685_) as u8);
    v_kind_boxed_1695_ = (leanh::lean_unbox(v_kind_1688_) as u8);
    v_res_1696_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(v_00_u03b1_1683_, v_name_1684_, v_bi_boxed_1694_, v_type_1686_, v_k_1687_, v_kind_boxed_1695_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
    leanh::lean_dec(v___y_1692_);
    leanh::lean_dec_ref(v___y_1691_);
    leanh::lean_dec(v___y_1690_);
    leanh::lean_dec_ref(v___y_1689_);
    return v_res_1696_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(
    mut v_00_u03b1_1697_: *mut leanh::LeanObject,
    mut v_name_1698_: *mut leanh::LeanObject,
    mut v_type_1699_: *mut leanh::LeanObject,
    mut v_k_1700_: *mut leanh::LeanObject,
    mut v___y_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
    mut v___y_1704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_1698_, v_type_1699_, v_k_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___boxed(
    mut v_00_u03b1_1707_: *mut leanh::LeanObject,
    mut v_name_1708_: *mut leanh::LeanObject,
    mut v_type_1709_: *mut leanh::LeanObject,
    mut v_k_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
    mut v___y_1713_: *mut leanh::LeanObject,
    mut v___y_1714_: *mut leanh::LeanObject,
    mut v___y_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1716_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(v_00_u03b1_1707_, v_name_1708_, v_type_1709_, v_k_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
    leanh::lean_dec(v___y_1714_);
    leanh::lean_dec_ref(v___y_1713_);
    leanh::lean_dec(v___y_1712_);
    leanh::lean_dec_ref(v___y_1711_);
    return v_res_1716_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(
    mut v_type_1717_: *mut leanh::LeanObject,
    mut v_k_1718_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1719_: u8,
    mut v_whnfType_1720_: u8,
    mut v___y_1721_: *mut leanh::LeanObject,
    mut v___y_1722_: *mut leanh::LeanObject,
    mut v___y_1723_: *mut leanh::LeanObject,
    mut v___y_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut v_a_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1726_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_1726_, 0, v_k_1718_);
                v___x_1727_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    leanh::lean_box(0),
                    v_type_1717_,
                    v___f_1726_,
                    v_cleanupAnnotations_1719_,
                    v_whnfType_1720_,
                    v___y_1721_,
                    v___y_1722_,
                    v___y_1723_,
                    v___y_1724_,
                );
                if leanh::lean_obj_tag(v___x_1727_) == 0 {
                    v_a_1728_ = leanh::lean_ctor_get(v___x_1727_, 0);
                    v_isSharedCheck_1735_ = (!leanh::lean_is_exclusive(v___x_1727_)) as u8;
                    if v_isSharedCheck_1735_ == 0 {
                        v___x_1730_ = v___x_1727_;
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1728_);
                        leanh::lean_dec(v___x_1727_);
                        v___x_1730_ = leanh::lean_box(0);
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1736_ = leanh::lean_ctor_get(v___x_1727_, 0);
                    v_isSharedCheck_1743_ = (!leanh::lean_is_exclusive(v___x_1727_)) as u8;
                    if v_isSharedCheck_1743_ == 0 {
                        v___x_1738_ = v___x_1727_;
                        v_isShared_1739_ = v_isSharedCheck_1743_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1736_);
                        leanh::lean_dec(v___x_1727_);
                        v___x_1738_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1734_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
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
                    v_reuseFailAlloc_1742_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
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
    mut v_type_1744_: *mut leanh::LeanObject,
    mut v_k_1745_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1746_: *mut leanh::LeanObject,
    mut v_whnfType_1747_: *mut leanh::LeanObject,
    mut v___y_1748_: *mut leanh::LeanObject,
    mut v___y_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1753_: u8 = 0;
    let mut v_whnfType_boxed_1754_: u8 = 0;
    let mut v_res_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1753_ = (leanh::lean_unbox(v_cleanupAnnotations_1746_) as u8);
    v_whnfType_boxed_1754_ = (leanh::lean_unbox(v_whnfType_1747_) as u8);
    v_res_1755_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_1744_, v_k_1745_, v_cleanupAnnotations_boxed_1753_, v_whnfType_boxed_1754_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
    leanh::lean_dec(v___y_1751_);
    leanh::lean_dec_ref(v___y_1750_);
    leanh::lean_dec(v___y_1749_);
    leanh::lean_dec_ref(v___y_1748_);
    return v_res_1755_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(
    mut v_00_u03b1_1756_: *mut leanh::LeanObject,
    mut v_type_1757_: *mut leanh::LeanObject,
    mut v_k_1758_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1759_: u8,
    mut v_whnfType_1760_: u8,
    mut v___y_1761_: *mut leanh::LeanObject,
    mut v___y_1762_: *mut leanh::LeanObject,
    mut v___y_1763_: *mut leanh::LeanObject,
    mut v___y_1764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1766_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_1757_, v_k_1758_, v_cleanupAnnotations_1759_, v_whnfType_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
    return v___x_1766_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___boxed(
    mut v_00_u03b1_1767_: *mut leanh::LeanObject,
    mut v_type_1768_: *mut leanh::LeanObject,
    mut v_k_1769_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1770_: *mut leanh::LeanObject,
    mut v_whnfType_1771_: *mut leanh::LeanObject,
    mut v___y_1772_: *mut leanh::LeanObject,
    mut v___y_1773_: *mut leanh::LeanObject,
    mut v___y_1774_: *mut leanh::LeanObject,
    mut v___y_1775_: *mut leanh::LeanObject,
    mut v___y_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1777_: u8 = 0;
    let mut v_whnfType_boxed_1778_: u8 = 0;
    let mut v_res_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1777_ = (leanh::lean_unbox(v_cleanupAnnotations_1770_) as u8);
    v_whnfType_boxed_1778_ = (leanh::lean_unbox(v_whnfType_1771_) as u8);
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
    leanh::lean_dec(v___y_1775_);
    leanh::lean_dec_ref(v___y_1774_);
    leanh::lean_dec(v___y_1773_);
    leanh::lean_dec_ref(v___y_1772_);
    return v_res_1779_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ =
        l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0;
    v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
    return v___x_1782_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(
    mut v_constName_1783_: *mut leanh::LeanObject,
    mut v___y_1784_: *mut leanh::LeanObject,
    mut v___y_1785_: *mut leanh::LeanObject,
    mut v___y_1786_: *mut leanh::LeanObject,
    mut v___y_1787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1789_ = lean_st_ref_get(v___y_1787_);
                v_env_1790_ = leanh::lean_ctor_get(v___x_1789_, 0);
                leanh::lean_inc_ref(v_env_1790_);
                leanh::lean_dec(v___x_1789_);
                leanh::lean_inc(v_constName_1783_);
                v___x_1791_ = l_Lean_isInductiveCore_x3f(v_env_1790_, v_constName_1783_);
                if leanh::lean_obj_tag(v___x_1791_) == 0 {
                    v___x_1792_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
                    v___x_1793_ = 0;
                    v___x_1794_ = l_Lean_MessageData_ofConstName(v_constName_1783_, v___x_1793_);
                    v___x_1795_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1795_, 0, v___x_1792_);
                    leanh::lean_ctor_set(v___x_1795_, 1, v___x_1794_);
                    v___x_1796_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1);
                    v___x_1797_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1797_, 0, v___x_1795_);
                    leanh::lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                    v___x_1798_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_1797_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
                    return v___x_1798_;
                } else {
                    leanh::lean_dec(v_constName_1783_);
                    v_val_1799_ = leanh::lean_ctor_get(v___x_1791_, 0);
                    v_isSharedCheck_1806_ = (!leanh::lean_is_exclusive(v___x_1791_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v___x_1801_ = v___x_1791_;
                        v_isShared_1802_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1799_);
                        leanh::lean_dec(v___x_1791_);
                        v___x_1801_ = leanh::lean_box(0);
                        v_isShared_1802_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1802_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1801_, 0);
                    v___x_1804_ = v___x_1801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_val_1799_);
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
    mut v_constName_1807_: *mut leanh::LeanObject,
    mut v___y_1808_: *mut leanh::LeanObject,
    mut v___y_1809_: *mut leanh::LeanObject,
    mut v___y_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
    mut v___y_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(
        v_constName_1807_,
        v___y_1808_,
        v___y_1809_,
        v___y_1810_,
        v___y_1811_,
    );
    leanh::lean_dec(v___y_1811_);
    leanh::lean_dec_ref(v___y_1810_);
    leanh::lean_dec(v___y_1809_);
    leanh::lean_dec_ref(v___y_1808_);
    return v_res_1813_;
}
pub unsafe fn _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = leanh::lean_box(0);
    v_dummy_1815_ = l_Lean_Expr_sort___override(v___x_1814_);
    return v_dummy_1815_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(
    mut v_ctor_1818_: *mut leanh::LeanObject,
    mut v_k_1819_: *mut leanh::LeanObject,
    mut v_zs_1820_: *mut leanh::LeanObject,
    mut v_ctorRet_1821_: *mut leanh::LeanObject,
    mut v___y_1822_: *mut leanh::LeanObject,
    mut v___y_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1854_: u8 = 0;
    let mut v_a_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_a_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_a_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1825_);
                leanh::lean_inc_ref(v___y_1824_);
                leanh::lean_inc(v___y_1823_);
                leanh::lean_inc_ref(v___y_1822_);
                v___x_1827_ = lean_whnf(
                    v_ctorRet_1821_,
                    v___y_1822_,
                    v___y_1823_,
                    v___y_1824_,
                    v___y_1825_,
                );
                if leanh::lean_obj_tag(v___x_1827_) == 0 {
                    v_a_1828_ = leanh::lean_ctor_get(v___x_1827_, 0);
                    leanh::lean_inc(v_a_1828_);
                    leanh::lean_dec_ref_known(v___x_1827_, 1);
                    v___x_1829_ = l_Lean_Core_betaReduce(v_a_1828_, v___y_1824_, v___y_1825_);
                    if leanh::lean_obj_tag(v___x_1829_) == 0 {
                        v_a_1830_ = leanh::lean_ctor_get(v___x_1829_, 0);
                        leanh::lean_inc(v_a_1830_);
                        leanh::lean_dec_ref_known(v___x_1829_, 1);
                        v___x_1831_ = l_Lean_Expr_getAppFn(v_a_1830_);
                        v___x_1832_ = l_Lean_Expr_constName_x21(v___x_1831_);
                        leanh::lean_dec_ref(v___x_1831_);
                        v___x_1833_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v___x_1832_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
                        if leanh::lean_obj_tag(v___x_1833_) == 0 {
                            v_a_1834_ = leanh::lean_ctor_get(v___x_1833_, 0);
                            leanh::lean_inc(v_a_1834_);
                            leanh::lean_dec_ref_known(v___x_1833_, 1);
                            v_numIndices_1835_ = leanh::lean_ctor_get(v_a_1834_, 2);
                            leanh::lean_inc(v_numIndices_1835_);
                            leanh::lean_dec(v_a_1834_);
                            v___x_1836_ = l_Lean_Expr_getAppFn(v_ctor_1818_);
                            v___x_1837_ = l_Lean_Expr_constName_x21(v___x_1836_);
                            leanh::lean_dec_ref(v___x_1836_);
                            v___x_1838_ = l_Lean_Meta_occursInCtorTypeMask(
                                v___x_1837_,
                                v___y_1822_,
                                v___y_1823_,
                                v___y_1824_,
                                v___y_1825_,
                            );
                            if leanh::lean_obj_tag(v___x_1838_) == 0 {
                                v_a_1839_ = leanh::lean_ctor_get(v___x_1838_, 0);
                                leanh::lean_inc(v_a_1839_);
                                leanh::lean_dec_ref_known(v___x_1838_, 1);
                                v_dummy_1840_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once), _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0);
                                leanh::lean_inc(v_numIndices_1835_);
                                v___x_1841_ = lean_mk_array(v_numIndices_1835_, v_dummy_1840_);
                                v___x_1842_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(
                                    v_numIndices_1835_,
                                    v_a_1830_,
                                    v___x_1841_,
                                );
                                v___x_1843_ =
                                    l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1;
                                v___x_1844_ = lean_array_to_list(v_a_1839_);
                                leanh::lean_inc_ref_n(v_zs_1820_, 2);
                                v___x_1845_ = lean_array_to_list(v_zs_1820_);
                                v___x_1846_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_1818_, v_k_1819_, v_zs_1820_, v___x_1842_, v___x_1843_, v___x_1844_, v___x_1845_, v_zs_1820_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
                                return v___x_1846_;
                            } else {
                                leanh::lean_dec(v_numIndices_1835_);
                                leanh::lean_dec(v_a_1830_);
                                leanh::lean_dec_ref(v_zs_1820_);
                                leanh::lean_dec_ref(v_k_1819_);
                                leanh::lean_dec_ref(v_ctor_1818_);
                                v_a_1847_ = leanh::lean_ctor_get(v___x_1838_, 0);
                                v_isSharedCheck_1854_ =
                                    (!leanh::lean_is_exclusive(v___x_1838_)) as u8;
                                if v_isSharedCheck_1854_ == 0 {
                                    v___x_1849_ = v___x_1838_;
                                    v_isShared_1850_ = v_isSharedCheck_1854_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1847_);
                                    leanh::lean_dec(v___x_1838_);
                                    v___x_1849_ = leanh::lean_box(0);
                                    v_isShared_1850_ = v_isSharedCheck_1854_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1830_);
                            leanh::lean_dec_ref(v_zs_1820_);
                            leanh::lean_dec_ref(v_k_1819_);
                            leanh::lean_dec_ref(v_ctor_1818_);
                            v_a_1855_ = leanh::lean_ctor_get(v___x_1833_, 0);
                            v_isSharedCheck_1862_ =
                                (!leanh::lean_is_exclusive(v___x_1833_)) as u8;
                            if v_isSharedCheck_1862_ == 0 {
                                v___x_1857_ = v___x_1833_;
                                v_isShared_1858_ = v_isSharedCheck_1862_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1855_);
                                leanh::lean_dec(v___x_1833_);
                                v___x_1857_ = leanh::lean_box(0);
                                v_isShared_1858_ = v_isSharedCheck_1862_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_zs_1820_);
                        leanh::lean_dec_ref(v_k_1819_);
                        leanh::lean_dec_ref(v_ctor_1818_);
                        v_a_1863_ = leanh::lean_ctor_get(v___x_1829_, 0);
                        v_isSharedCheck_1870_ =
                            (!leanh::lean_is_exclusive(v___x_1829_)) as u8;
                        if v_isSharedCheck_1870_ == 0 {
                            v___x_1865_ = v___x_1829_;
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1863_);
                            leanh::lean_dec(v___x_1829_);
                            v___x_1865_ = leanh::lean_box(0);
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_zs_1820_);
                    leanh::lean_dec_ref(v_k_1819_);
                    leanh::lean_dec_ref(v_ctor_1818_);
                    v_a_1871_ = leanh::lean_ctor_get(v___x_1827_, 0);
                    v_isSharedCheck_1878_ = (!leanh::lean_is_exclusive(v___x_1827_)) as u8;
                    if v_isSharedCheck_1878_ == 0 {
                        v___x_1873_ = v___x_1827_;
                        v_isShared_1874_ = v_isSharedCheck_1878_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1871_);
                        leanh::lean_dec(v___x_1827_);
                        v___x_1873_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1853_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
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
                    v_reuseFailAlloc_1861_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
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
                    v_reuseFailAlloc_1869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
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
                    v_reuseFailAlloc_1877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
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
    mut v_ctor_1879_: *mut leanh::LeanObject,
    mut v_k_1880_: *mut leanh::LeanObject,
    mut v_zs_1881_: *mut leanh::LeanObject,
    mut v_ctorRet_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1886_);
    leanh::lean_dec_ref(v___y_1885_);
    leanh::lean_dec(v___y_1884_);
    leanh::lean_dec_ref(v___y_1883_);
    return v_res_1888_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices___redArg(
    mut v_ctor_1889_: *mut leanh::LeanObject,
    mut v_k_1890_: *mut leanh::LeanObject,
    mut v_a_1891_: *mut leanh::LeanObject,
    mut v_a_1892_: *mut leanh::LeanObject,
    mut v_a_1893_: *mut leanh::LeanObject,
    mut v_a_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: u8 = 0;
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_1894_);
                leanh::lean_inc_ref(v_a_1893_);
                leanh::lean_inc(v_a_1892_);
                leanh::lean_inc_ref(v_a_1891_);
                leanh::lean_inc_ref(v_ctor_1889_);
                v___x_1896_ =
                    lean_infer_type(v_ctor_1889_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
                if leanh::lean_obj_tag(v___x_1896_) == 0 {
                    v_a_1897_ = leanh::lean_ctor_get(v___x_1896_, 0);
                    leanh::lean_inc(v_a_1897_);
                    leanh::lean_dec_ref_known(v___x_1896_, 1);
                    v___f_1898_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1898_, 0, v_ctor_1889_);
                    leanh::lean_closure_set(v___f_1898_, 1, v_k_1890_);
                    v___x_1899_ = 0;
                    v___x_1900_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_a_1897_, v___f_1898_, v___x_1899_, v___x_1899_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
                    return v___x_1900_;
                } else {
                    leanh::lean_dec_ref(v_k_1890_);
                    leanh::lean_dec_ref(v_ctor_1889_);
                    v_a_1901_ = leanh::lean_ctor_get(v___x_1896_, 0);
                    v_isSharedCheck_1908_ = (!leanh::lean_is_exclusive(v___x_1896_)) as u8;
                    if v_isSharedCheck_1908_ == 0 {
                        v___x_1903_ = v___x_1896_;
                        v_isShared_1904_ = v_isSharedCheck_1908_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1901_);
                        leanh::lean_dec(v___x_1896_);
                        v___x_1903_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
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
    mut v_ctor_1909_: *mut leanh::LeanObject,
    mut v_k_1910_: *mut leanh::LeanObject,
    mut v_a_1911_: *mut leanh::LeanObject,
    mut v_a_1912_: *mut leanh::LeanObject,
    mut v_a_1913_: *mut leanh::LeanObject,
    mut v_a_1914_: *mut leanh::LeanObject,
    mut v_a_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1916_ = l_Lean_Meta_withSharedCtorIndices___redArg(
        v_ctor_1909_,
        v_k_1910_,
        v_a_1911_,
        v_a_1912_,
        v_a_1913_,
        v_a_1914_,
    );
    leanh::lean_dec(v_a_1914_);
    leanh::lean_dec_ref(v_a_1913_);
    leanh::lean_dec(v_a_1912_);
    leanh::lean_dec_ref(v_a_1911_);
    return v_res_1916_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices(
    mut v_00_u03b1_1917_: *mut leanh::LeanObject,
    mut v_ctor_1918_: *mut leanh::LeanObject,
    mut v_k_1919_: *mut leanh::LeanObject,
    mut v_a_1920_: *mut leanh::LeanObject,
    mut v_a_1921_: *mut leanh::LeanObject,
    mut v_a_1922_: *mut leanh::LeanObject,
    mut v_a_1923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1926_: *mut leanh::LeanObject,
    mut v_ctor_1927_: *mut leanh::LeanObject,
    mut v_k_1928_: *mut leanh::LeanObject,
    mut v_a_1929_: *mut leanh::LeanObject,
    mut v_a_1930_: *mut leanh::LeanObject,
    mut v_a_1931_: *mut leanh::LeanObject,
    mut v_a_1932_: *mut leanh::LeanObject,
    mut v_a_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Lean_Meta_withSharedCtorIndices(
        v_00_u03b1_1926_,
        v_ctor_1927_,
        v_k_1928_,
        v_a_1929_,
        v_a_1930_,
        v_a_1931_,
        v_a_1932_,
    );
    leanh::lean_dec(v_a_1932_);
    leanh::lean_dec_ref(v_a_1931_);
    leanh::lean_dec(v_a_1930_);
    leanh::lean_dec_ref(v_a_1929_);
    return v_res_1934_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_SameCtorUtils(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_SameCtorUtils(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_SameCtorUtils(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_SameCtorUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_SameCtorUtils(builtin);
}