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
    lean_array_push, lean_array_to_list, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::lean_imports_rs::Lean::Util::FindExpr::lean_find_expr;
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_occursInCtorTypeMask___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_occursInCtorTypeMask___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_occursInCtorTypeMask___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 116, 46, 105, 115, 70, 111, 114, 97, 108, 108, 10, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value: crate::leanh::LeanStringObject<70> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 97, 109, 101, 67, 116, 111, 114, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 119, 105, 116, 104, 83, 104, 97, 114, 101, 100, 67, 116, 111, 114, 73, 110, 100, 105, 99, 101, 115, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 97, 109, 101, 67, 116, 111, 114, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value:
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
static mut l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(
    mut v_lctx_968_: *mut crate::leanh::LeanObject,
    mut v_e_969_: *mut crate::leanh::LeanObject,
    mut v_s_970_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_s_970_) == 1 {
        let mut v_fvarId_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fvarId_971_ = crate::leanh::lean_ctor_get(v_s_970_, 0);
        crate::leanh::lean_inc(v_fvarId_971_);
        v___x_972_ = lean_local_ctx_find(v_lctx_968_, v_fvarId_971_);
        if crate::leanh::lean_obj_tag(v___x_972_) == 1 {
            let mut v_val_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_974_: u8 = 0;
            v_val_973_ = crate::leanh::lean_ctor_get(v___x_972_, 0);
            crate::leanh::lean_inc(v_val_973_);
            crate::leanh::lean_dec_ref_known(v___x_972_, 1);
            v___x_974_ = lean_expr_eqv(v_s_970_, v_e_969_);
            crate::leanh::lean_dec_ref_known(v_s_970_, 1);
            if v___x_974_ == 0 {
                let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_976_: u8 = 0;
                v___x_975_ = l_Lean_LocalDecl_type(v_val_973_);
                crate::leanh::lean_dec(v_val_973_);
                v___x_976_ = l_Lean_Expr_occurs(v_e_969_, v___x_975_);
                crate::leanh::lean_dec_ref(v___x_975_);
                return v___x_976_;
            } else {
                crate::leanh::lean_dec(v_val_973_);
                crate::leanh::lean_dec_ref(v_e_969_);
                return v___x_974_;
            }
        } else {
            let mut v___x_977_: u8 = 0;
            crate::leanh::lean_dec(v___x_972_);
            v___x_977_ = lean_expr_eqv(v_s_970_, v_e_969_);
            crate::leanh::lean_dec_ref(v_e_969_);
            crate::leanh::lean_dec_ref_known(v_s_970_, 1);
            return v___x_977_;
        }
    } else {
        let mut v___x_978_: u8 = 0;
        crate::leanh::lean_dec_ref(v_lctx_968_);
        v___x_978_ = lean_expr_eqv(v_s_970_, v_e_969_);
        crate::leanh::lean_dec_ref(v_e_969_);
        crate::leanh::lean_dec_ref(v_s_970_);
        return v___x_978_;
    }
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed(
    mut v_lctx_979_: *mut crate::leanh::LeanObject,
    mut v_e_980_: *mut crate::leanh::LeanObject,
    mut v_s_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: u8 = 0;
    let mut v_r_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(
        v_lctx_979_,
        v_e_980_,
        v_s_981_,
    );
    v_r_983_ = crate::leanh::lean_box((v_res_982_) as usize);
    return v_r_983_;
}
pub unsafe fn l_Lean_Meta_occursOrInType(
    mut v_lctx_984_: *mut crate::leanh::LeanObject,
    mut v_e_985_: *mut crate::leanh::LeanObject,
    mut v_t_986_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_987_, 0, v_lctx_984_);
    crate::leanh::lean_closure_set(v___x_987_, 1, v_e_985_);
    v___x_988_ = lean_find_expr(v___x_987_, v_t_986_);
    crate::leanh::lean_dec_ref(v___x_987_);
    if crate::leanh::lean_obj_tag(v___x_988_) == 0 {
        let mut v___x_989_: u8 = 0;
        v___x_989_ = 0;
        return v___x_989_;
    } else {
        let mut v___x_990_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_988_, 1);
        v___x_990_ = 1;
        return v___x_990_;
    }
}
pub unsafe fn l_Lean_Meta_occursOrInType___boxed(
    mut v_lctx_991_: *mut crate::leanh::LeanObject,
    mut v_e_992_: *mut crate::leanh::LeanObject,
    mut v_t_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_994_: u8 = 0;
    let mut v_r_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Lean_Meta_occursOrInType(v_lctx_991_, v_e_992_, v_t_993_);
    crate::leanh::lean_dec_ref(v_t_993_);
    v_r_995_ = crate::leanh::lean_box((v_res_994_) as usize);
    return v_r_995_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(
    mut v_k_996_: *mut crate::leanh::LeanObject,
    mut v_b_997_: *mut crate::leanh::LeanObject,
    mut v_c_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
    mut v___y_1001_: *mut crate::leanh::LeanObject,
    mut v___y_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1002_);
    crate::leanh::lean_inc_ref(v___y_1001_);
    crate::leanh::lean_inc(v___y_1000_);
    crate::leanh::lean_inc_ref(v___y_999_);
    v___x_1004_ = crate::leanh::lean_apply_7(
        v_k_996_,
        v_b_997_,
        v_c_998_,
        v___y_999_,
        v___y_1000_,
        v___y_1001_,
        v___y_1002_,
        crate::leanh::lean_box(0),
    );
    return v___x_1004_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed(
    mut v_k_1005_: *mut crate::leanh::LeanObject,
    mut v_b_1006_: *mut crate::leanh::LeanObject,
    mut v_c_1007_: *mut crate::leanh::LeanObject,
    mut v___y_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
    mut v___y_1010_: *mut crate::leanh::LeanObject,
    mut v___y_1011_: *mut crate::leanh::LeanObject,
    mut v___y_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(v_k_1005_, v_b_1006_, v_c_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
    crate::leanh::lean_dec(v___y_1011_);
    crate::leanh::lean_dec_ref(v___y_1010_);
    crate::leanh::lean_dec(v___y_1009_);
    crate::leanh::lean_dec_ref(v___y_1008_);
    return v_res_1013_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(
    mut v_type_1014_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1015_: *mut crate::leanh::LeanObject,
    mut v_k_1016_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1017_: u8,
    mut v_whnfType_1018_: u8,
    mut v___y_1019_: *mut crate::leanh::LeanObject,
    mut v___y_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
    mut v___y_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1033_: u8 = 0;
    let mut v_a_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1024_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1024_, 0, v_k_1016_);
                v___x_1025_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
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
                if crate::leanh::lean_obj_tag(v___x_1025_) == 0 {
                    v_a_1026_ = crate::leanh::lean_ctor_get(v___x_1025_, 0);
                    v_isSharedCheck_1033_ = (!crate::leanh::lean_is_exclusive(v___x_1025_)) as u8;
                    if v_isSharedCheck_1033_ == 0 {
                        v___x_1028_ = v___x_1025_;
                        v_isShared_1029_ = v_isSharedCheck_1033_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1026_);
                        crate::leanh::lean_dec(v___x_1025_);
                        v___x_1028_ = crate::leanh::lean_box(0);
                        v_isShared_1029_ = v_isSharedCheck_1033_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1034_ = crate::leanh::lean_ctor_get(v___x_1025_, 0);
                    v_isSharedCheck_1041_ = (!crate::leanh::lean_is_exclusive(v___x_1025_)) as u8;
                    if v_isSharedCheck_1041_ == 0 {
                        v___x_1036_ = v___x_1025_;
                        v_isShared_1037_ = v_isSharedCheck_1041_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1034_);
                        crate::leanh::lean_dec(v___x_1025_);
                        v___x_1036_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1032_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
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
                    v_reuseFailAlloc_1040_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
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
    mut v_type_1042_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1043_: *mut crate::leanh::LeanObject,
    mut v_k_1044_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1045_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1046_: *mut crate::leanh::LeanObject,
    mut v___y_1047_: *mut crate::leanh::LeanObject,
    mut v___y_1048_: *mut crate::leanh::LeanObject,
    mut v___y_1049_: *mut crate::leanh::LeanObject,
    mut v___y_1050_: *mut crate::leanh::LeanObject,
    mut v___y_1051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1052_: u8 = 0;
    let mut v_whnfType_boxed_1053_: u8 = 0;
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1052_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1045_) as u8);
    v_whnfType_boxed_1053_ = (crate::leanh::lean_unbox(v_whnfType_1046_) as u8);
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
    crate::leanh::lean_dec(v___y_1050_);
    crate::leanh::lean_dec_ref(v___y_1049_);
    crate::leanh::lean_dec(v___y_1048_);
    crate::leanh::lean_dec_ref(v___y_1047_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(
    mut v_00_u03b1_1055_: *mut crate::leanh::LeanObject,
    mut v_type_1056_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1057_: *mut crate::leanh::LeanObject,
    mut v_k_1058_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1059_: u8,
    mut v_whnfType_1060_: u8,
    mut v___y_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1067_: *mut crate::leanh::LeanObject,
    mut v_type_1068_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1069_: *mut crate::leanh::LeanObject,
    mut v_k_1070_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1071_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
    mut v___y_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1078_: u8 = 0;
    let mut v_whnfType_boxed_1079_: u8 = 0;
    let mut v_res_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1078_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1071_) as u8);
    v_whnfType_boxed_1079_ = (crate::leanh::lean_unbox(v_whnfType_1072_) as u8);
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
    crate::leanh::lean_dec(v___y_1076_);
    crate::leanh::lean_dec_ref(v___y_1075_);
    crate::leanh::lean_dec(v___y_1074_);
    crate::leanh::lean_dec_ref(v___y_1073_);
    return v_res_1080_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(
    mut v___x_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_sz_1083_: usize,
    mut v_i_1084_: usize,
    mut v_bs_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1086_: u8 = 0;
    let mut v_v_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1091_: usize = 0;
    let mut v___x_1092_: usize = 0;
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1086_ = lean_usize_dec_lt(v_i_1084_, v_sz_1083_);
                if v___x_1086_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1081_);
                    return v_bs_1085_;
                } else {
                    v_v_1087_ = lean_array_uget(v_bs_1085_, v_i_1084_);
                    v___x_1088_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1089_ = lean_array_uset(v_bs_1085_, v_i_1084_, v___x_1088_);
                    crate::leanh::lean_inc_ref(v___x_1081_);
                    v___x_1090_ = l_Lean_Meta_occursOrInType(v___x_1081_, v_v_1087_, v_a_1082_);
                    v___x_1091_ = 1usize;
                    v___x_1092_ = lean_usize_add(v_i_1084_, v___x_1091_);
                    v___x_1093_ = crate::leanh::lean_box((v___x_1090_) as usize);
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
    mut v___x_1096_: *mut crate::leanh::LeanObject,
    mut v_a_1097_: *mut crate::leanh::LeanObject,
    mut v_sz_1098_: *mut crate::leanh::LeanObject,
    mut v_i_1099_: *mut crate::leanh::LeanObject,
    mut v_bs_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1101_: usize = 0;
    let mut v_i_boxed_1102_: usize = 0;
    let mut v_res_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1101_ = crate::leanh::lean_unbox_usize(v_sz_1098_);
    crate::leanh::lean_dec(v_sz_1098_);
    v_i_boxed_1102_ = crate::leanh::lean_unbox_usize(v_i_1099_);
    crate::leanh::lean_dec(v_i_1099_);
    v_res_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v___x_1096_, v_a_1097_, v_sz_boxed_1101_, v_i_boxed_1102_, v_bs_1100_);
    crate::leanh::lean_dec_ref(v_a_1097_);
    return v_res_1103_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask___lam__0(
    mut v_ys_1104_: *mut crate::leanh::LeanObject,
    mut v_ctorRet_1105_: *mut crate::leanh::LeanObject,
    mut v___y_1106_: *mut crate::leanh::LeanObject,
    mut v___y_1107_: *mut crate::leanh::LeanObject,
    mut v___y_1108_: *mut crate::leanh::LeanObject,
    mut v___y_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v_lctx_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1119_: usize = 0;
    let mut v___x_1120_: usize = 0;
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut v_a_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1129_: u8 = 0;
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1133_: u8 = 0;
    let mut v_a_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1137_: u8 = 0;
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1109_);
                crate::leanh::lean_inc_ref(v___y_1108_);
                crate::leanh::lean_inc(v___y_1107_);
                crate::leanh::lean_inc_ref(v___y_1106_);
                v___x_1111_ = lean_whnf(
                    v_ctorRet_1105_,
                    v___y_1106_,
                    v___y_1107_,
                    v___y_1108_,
                    v___y_1109_,
                );
                if crate::leanh::lean_obj_tag(v___x_1111_) == 0 {
                    v_a_1112_ = crate::leanh::lean_ctor_get(v___x_1111_, 0);
                    crate::leanh::lean_inc(v_a_1112_);
                    crate::leanh::lean_dec_ref_known(v___x_1111_, 1);
                    v___x_1113_ = l_Lean_Core_betaReduce(v_a_1112_, v___y_1108_, v___y_1109_);
                    if crate::leanh::lean_obj_tag(v___x_1113_) == 0 {
                        v_a_1114_ = crate::leanh::lean_ctor_get(v___x_1113_, 0);
                        v_isSharedCheck_1125_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1113_)) as u8;
                        if v_isSharedCheck_1125_ == 0 {
                            v___x_1116_ = v___x_1113_;
                            v_isShared_1117_ = v_isSharedCheck_1125_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1114_);
                            crate::leanh::lean_dec(v___x_1113_);
                            v___x_1116_ = crate::leanh::lean_box(0);
                            v_isShared_1117_ = v_isSharedCheck_1125_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ys_1104_);
                        v_a_1126_ = crate::leanh::lean_ctor_get(v___x_1113_, 0);
                        v_isSharedCheck_1133_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1113_)) as u8;
                        if v_isSharedCheck_1133_ == 0 {
                            v___x_1128_ = v___x_1113_;
                            v_isShared_1129_ = v_isSharedCheck_1133_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1126_);
                            crate::leanh::lean_dec(v___x_1113_);
                            v___x_1128_ = crate::leanh::lean_box(0);
                            v_isShared_1129_ = v_isSharedCheck_1133_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ys_1104_);
                    v_a_1134_ = crate::leanh::lean_ctor_get(v___x_1111_, 0);
                    v_isSharedCheck_1141_ = (!crate::leanh::lean_is_exclusive(v___x_1111_)) as u8;
                    if v_isSharedCheck_1141_ == 0 {
                        v___x_1136_ = v___x_1111_;
                        v_isShared_1137_ = v_isSharedCheck_1141_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1134_);
                        crate::leanh::lean_dec(v___x_1111_);
                        v___x_1136_ = crate::leanh::lean_box(0);
                        v_isShared_1137_ = v_isSharedCheck_1141_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_lctx_1118_ = crate::leanh::lean_ctor_get(v___y_1106_, 2);
                v_sz_1119_ = lean_array_size(v_ys_1104_);
                v___x_1120_ = 0usize;
                crate::leanh::lean_inc_ref(v_lctx_1118_);
                v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v_lctx_1118_, v_a_1114_, v_sz_1119_, v___x_1120_, v_ys_1104_);
                crate::leanh::lean_dec(v_a_1114_);
                if v_isShared_1117_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1116_, 0, v___x_1121_);
                    v___x_1123_ = v___x_1116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
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
                    v_reuseFailAlloc_1132_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
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
                    v_reuseFailAlloc_1140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
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
    mut v_ys_1142_: *mut crate::leanh::LeanObject,
    mut v_ctorRet_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
    mut v___y_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Lean_Meta_occursInCtorTypeMask___lam__0(
        v_ys_1142_,
        v_ctorRet_1143_,
        v___y_1144_,
        v___y_1145_,
        v___y_1146_,
        v___y_1147_,
    );
    crate::leanh::lean_dec(v___y_1147_);
    crate::leanh::lean_dec_ref(v___y_1146_);
    crate::leanh::lean_dec(v___y_1145_);
    crate::leanh::lean_dec_ref(v___y_1144_);
    return v_res_1149_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask___lam__1(
    mut v_numFields_1150_: *mut crate::leanh::LeanObject,
    mut v___f_1151_: *mut crate::leanh::LeanObject,
    mut v_x_1152_: *mut crate::leanh::LeanObject,
    mut v_ctorRet_1153_: *mut crate::leanh::LeanObject,
    mut v___y_1154_: *mut crate::leanh::LeanObject,
    mut v___y_1155_: *mut crate::leanh::LeanObject,
    mut v___y_1156_: *mut crate::leanh::LeanObject,
    mut v___y_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1159_, 0, v_numFields_1150_);
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
    mut v_numFields_1162_: *mut crate::leanh::LeanObject,
    mut v___f_1163_: *mut crate::leanh::LeanObject,
    mut v_x_1164_: *mut crate::leanh::LeanObject,
    mut v_ctorRet_1165_: *mut crate::leanh::LeanObject,
    mut v___y_1166_: *mut crate::leanh::LeanObject,
    mut v___y_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
    mut v___y_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1169_);
    crate::leanh::lean_dec_ref(v___y_1168_);
    crate::leanh::lean_dec(v___y_1167_);
    crate::leanh::lean_dec_ref(v___y_1166_);
    crate::leanh::lean_dec_ref(v_x_1164_);
    return v_res_1171_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1172_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(
    mut v_msg_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
    mut v___y_1179_: *mut crate::leanh::LeanObject,
    mut v___y_1180_: *mut crate::leanh::LeanObject,
    mut v___y_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1188_: u8 = 0;
    let mut v_toFunctor_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1195_: u8 = 0;
    let mut v___f_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1212_: u8 = 0;
    let mut v_toFunctor_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1219_: u8 = 0;
    let mut v___f_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065__overap_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut v_unused_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_unused_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v_unused_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1246_: u8 = 0;
    let mut v_unused_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1183_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0);
                v___x_1184_ = l_StateRefT_x27_instMonad___redArg(v___x_1183_);
                v_toApplicative_1185_ = crate::leanh::lean_ctor_get(v___x_1184_, 0);
                v_isSharedCheck_1246_ = (!crate::leanh::lean_is_exclusive(v___x_1184_)) as u8;
                if v_isSharedCheck_1246_ == 0 {
                    v_unused_1247_ = crate::leanh::lean_ctor_get(v___x_1184_, 1);
                    crate::leanh::lean_dec(v_unused_1247_);
                    v___x_1187_ = v___x_1184_;
                    v_isShared_1188_ = v_isSharedCheck_1246_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1185_);
                    crate::leanh::lean_dec(v___x_1184_);
                    v___x_1187_ = crate::leanh::lean_box(0);
                    v_isShared_1188_ = v_isSharedCheck_1246_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1189_ = crate::leanh::lean_ctor_get(v_toApplicative_1185_, 0);
                v_toSeq_1190_ = crate::leanh::lean_ctor_get(v_toApplicative_1185_, 2);
                v_toSeqLeft_1191_ = crate::leanh::lean_ctor_get(v_toApplicative_1185_, 3);
                v_toSeqRight_1192_ = crate::leanh::lean_ctor_get(v_toApplicative_1185_, 4);
                v_isSharedCheck_1244_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1185_)) as u8;
                if v_isSharedCheck_1244_ == 0 {
                    v_unused_1245_ = crate::leanh::lean_ctor_get(v_toApplicative_1185_, 1);
                    crate::leanh::lean_dec(v_unused_1245_);
                    v___x_1194_ = v_toApplicative_1185_;
                    v_isShared_1195_ = v_isSharedCheck_1244_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1192_);
                    crate::leanh::lean_inc(v_toSeqLeft_1191_);
                    crate::leanh::lean_inc(v_toSeq_1190_);
                    crate::leanh::lean_inc(v_toFunctor_1189_);
                    crate::leanh::lean_dec(v_toApplicative_1185_);
                    v___x_1194_ = crate::leanh::lean_box(0);
                    v_isShared_1195_ = v_isSharedCheck_1244_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1196_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1;
                v___f_1197_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_1189_);
                v___f_1198_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1198_, 0, v_toFunctor_1189_);
                v___f_1199_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1199_, 0, v_toFunctor_1189_);
                v___x_1200_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1200_, 0, v___f_1198_);
                crate::leanh::lean_ctor_set(v___x_1200_, 1, v___f_1199_);
                v___f_1201_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1201_, 0, v_toSeqRight_1192_);
                v___f_1202_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1202_, 0, v_toSeqLeft_1191_);
                v___f_1203_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1203_, 0, v_toSeq_1190_);
                if v_isShared_1195_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1194_, 4, v___f_1201_);
                    crate::leanh::lean_ctor_set(v___x_1194_, 3, v___f_1202_);
                    crate::leanh::lean_ctor_set(v___x_1194_, 2, v___f_1203_);
                    crate::leanh::lean_ctor_set(v___x_1194_, 1, v___f_1196_);
                    crate::leanh::lean_ctor_set(v___x_1194_, 0, v___x_1200_);
                    v___x_1205_ = v___x_1194_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___f_1196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 2, v___f_1203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 3, v___f_1202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 4, v___f_1201_);
                    v___x_1205_ = v_reuseFailAlloc_1243_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1187_, 1, v___f_1197_);
                    crate::leanh::lean_ctor_set(v___x_1187_, 0, v___x_1205_);
                    v___x_1207_ = v___x_1187_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___f_1197_);
                    v___x_1207_ = v_reuseFailAlloc_1242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1208_ = l_StateRefT_x27_instMonad___redArg(v___x_1207_);
                v_toApplicative_1209_ = crate::leanh::lean_ctor_get(v___x_1208_, 0);
                v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v___x_1208_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v_unused_1241_ = crate::leanh::lean_ctor_get(v___x_1208_, 1);
                    crate::leanh::lean_dec(v_unused_1241_);
                    v___x_1211_ = v___x_1208_;
                    v_isShared_1212_ = v_isSharedCheck_1240_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1209_);
                    crate::leanh::lean_dec(v___x_1208_);
                    v___x_1211_ = crate::leanh::lean_box(0);
                    v_isShared_1212_ = v_isSharedCheck_1240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1213_ = crate::leanh::lean_ctor_get(v_toApplicative_1209_, 0);
                v_toSeq_1214_ = crate::leanh::lean_ctor_get(v_toApplicative_1209_, 2);
                v_toSeqLeft_1215_ = crate::leanh::lean_ctor_get(v_toApplicative_1209_, 3);
                v_toSeqRight_1216_ = crate::leanh::lean_ctor_get(v_toApplicative_1209_, 4);
                v_isSharedCheck_1238_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1209_)) as u8;
                if v_isSharedCheck_1238_ == 0 {
                    v_unused_1239_ = crate::leanh::lean_ctor_get(v_toApplicative_1209_, 1);
                    crate::leanh::lean_dec(v_unused_1239_);
                    v___x_1218_ = v_toApplicative_1209_;
                    v_isShared_1219_ = v_isSharedCheck_1238_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1216_);
                    crate::leanh::lean_inc(v_toSeqLeft_1215_);
                    crate::leanh::lean_inc(v_toSeq_1214_);
                    crate::leanh::lean_inc(v_toFunctor_1213_);
                    crate::leanh::lean_dec(v_toApplicative_1209_);
                    v___x_1218_ = crate::leanh::lean_box(0);
                    v_isShared_1219_ = v_isSharedCheck_1238_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1220_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3;
                v___f_1221_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_1213_);
                v___f_1222_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1222_, 0, v_toFunctor_1213_);
                v___f_1223_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1223_, 0, v_toFunctor_1213_);
                v___x_1224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1224_, 0, v___f_1222_);
                crate::leanh::lean_ctor_set(v___x_1224_, 1, v___f_1223_);
                v___f_1225_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1225_, 0, v_toSeqRight_1216_);
                v___f_1226_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1226_, 0, v_toSeqLeft_1215_);
                v___f_1227_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1227_, 0, v_toSeq_1214_);
                if v_isShared_1219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1218_, 4, v___f_1225_);
                    crate::leanh::lean_ctor_set(v___x_1218_, 3, v___f_1226_);
                    crate::leanh::lean_ctor_set(v___x_1218_, 2, v___f_1227_);
                    crate::leanh::lean_ctor_set(v___x_1218_, 1, v___f_1220_);
                    crate::leanh::lean_ctor_set(v___x_1218_, 0, v___x_1224_);
                    v___x_1229_ = v___x_1218_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1237_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___f_1220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 2, v___f_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 3, v___f_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 4, v___f_1225_);
                    v___x_1229_ = v_reuseFailAlloc_1237_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1212_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1211_, 1, v___f_1221_);
                    crate::leanh::lean_ctor_set(v___x_1211_, 0, v___x_1229_);
                    v___x_1231_ = v___x_1211_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___f_1221_);
                    v___x_1231_ = v_reuseFailAlloc_1236_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1232_ = crate::leanh::lean_box(0);
                v___x_1233_ = l_instInhabitedOfMonad___redArg(v___x_1231_, v___x_1232_);
                v___x_2065__overap_1234_ = lean_panic_fn_borrowed(v___x_1233_, v_msg_1177_);
                crate::leanh::lean_dec(v___x_1233_);
                crate::leanh::lean_inc(v___y_1181_);
                crate::leanh::lean_inc_ref(v___y_1180_);
                crate::leanh::lean_inc(v___y_1179_);
                crate::leanh::lean_inc_ref(v___y_1178_);
                v___x_1235_ = crate::leanh::lean_apply_5(
                    v___x_2065__overap_1234_,
                    v___y_1178_,
                    v___y_1179_,
                    v___y_1180_,
                    v___y_1181_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___boxed(
    mut v_msg_1248_: *mut crate::leanh::LeanObject,
    mut v___y_1249_: *mut crate::leanh::LeanObject,
    mut v___y_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v_msg_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
    crate::leanh::lean_dec(v___y_1252_);
    crate::leanh::lean_dec_ref(v___y_1251_);
    crate::leanh::lean_dec(v___y_1250_);
    crate::leanh::lean_dec_ref(v___y_1249_);
    return v_res_1254_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(
    mut v_msgData_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = lean_st_ref_get(v___y_1259_);
    v_env_1262_ = crate::leanh::lean_ctor_get(v___x_1261_, 0);
    crate::leanh::lean_inc_ref(v_env_1262_);
    crate::leanh::lean_dec(v___x_1261_);
    v___x_1263_ = lean_st_ref_get(v___y_1257_);
    v_mctx_1264_ = crate::leanh::lean_ctor_get(v___x_1263_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1264_);
    crate::leanh::lean_dec(v___x_1263_);
    v_lctx_1265_ = crate::leanh::lean_ctor_get(v___y_1256_, 2);
    v_options_1266_ = crate::leanh::lean_ctor_get(v___y_1258_, 2);
    crate::leanh::lean_inc_ref(v_options_1266_);
    crate::leanh::lean_inc_ref(v_lctx_1265_);
    v___x_1267_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1267_, 0, v_env_1262_);
    crate::leanh::lean_ctor_set(v___x_1267_, 1, v_mctx_1264_);
    crate::leanh::lean_ctor_set(v___x_1267_, 2, v_lctx_1265_);
    crate::leanh::lean_ctor_set(v___x_1267_, 3, v_options_1266_);
    v___x_1268_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    crate::leanh::lean_ctor_set(v___x_1268_, 1, v_msgData_1255_);
    v___x_1269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1269_, 0, v___x_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msgData_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
    crate::leanh::lean_dec(v___y_1274_);
    crate::leanh::lean_dec_ref(v___y_1273_);
    crate::leanh::lean_dec(v___y_1272_);
    crate::leanh::lean_dec_ref(v___y_1271_);
    return v_res_1276_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(
    mut v_msg_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
    mut v___y_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1293_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1283_ = crate::leanh::lean_ctor_get(v___y_1280_, 5);
                v___x_1284_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msg_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
                v_a_1285_ = crate::leanh::lean_ctor_get(v___x_1284_, 0);
                v_isSharedCheck_1293_ = (!crate::leanh::lean_is_exclusive(v___x_1284_)) as u8;
                if v_isSharedCheck_1293_ == 0 {
                    v___x_1287_ = v___x_1284_;
                    v_isShared_1288_ = v_isSharedCheck_1293_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1285_);
                    crate::leanh::lean_dec(v___x_1284_);
                    v___x_1287_ = crate::leanh::lean_box(0);
                    v_isShared_1288_ = v_isSharedCheck_1293_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1283_);
                v___x_1289_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1289_, 0, v_ref_1283_);
                crate::leanh::lean_ctor_set(v___x_1289_, 1, v_a_1285_);
                if v_isShared_1288_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1287_, 1);
                    crate::leanh::lean_ctor_set(v___x_1287_, 0, v___x_1289_);
                    v___x_1291_ = v___x_1287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1292_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
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
    mut v_msg_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
    crate::leanh::lean_dec(v___y_1298_);
    crate::leanh::lean_dec_ref(v___y_1297_);
    crate::leanh::lean_dec(v___y_1296_);
    crate::leanh::lean_dec_ref(v___y_1295_);
    return v_res_1300_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0;
    v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2;
    v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
    return v___x_1306_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1310_ =
        l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6;
    v___x_1311_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1312_ = crate::leanh::lean_unsigned_to_nat(122);
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
    mut v_constName_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: u8 = 0;
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1335_: u8 = 0;
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v_val_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_a_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1330_ = lean_st_ref_get(v___y_1320_);
                v_env_1331_ = crate::leanh::lean_ctor_get(v___x_1330_, 0);
                crate::leanh::lean_inc_ref(v_env_1331_);
                crate::leanh::lean_dec(v___x_1330_);
                v___x_1332_ = 0;
                crate::leanh::lean_inc(v_constName_1316_);
                v___x_1333_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1331_, v_constName_1316_, v___x_1332_);
                if crate::leanh::lean_obj_tag(v___x_1333_) == 1 {
                    v_val_1334_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                    crate::leanh::lean_inc(v_val_1334_);
                    crate::leanh::lean_dec_ref_known(v___x_1333_, 1);
                    v_kind_1335_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_1334_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_1335_ == 6 {
                        v___x_1336_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1334_);
                        if crate::leanh::lean_obj_tag(v___x_1336_) == 6 {
                            crate::leanh::lean_dec(v_constName_1316_);
                            v_val_1337_ = crate::leanh::lean_ctor_get(v___x_1336_, 0);
                            v_isSharedCheck_1344_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1336_)) as u8;
                            if v_isSharedCheck_1344_ == 0 {
                                v___x_1339_ = v___x_1336_;
                                v_isShared_1340_ = v_isSharedCheck_1344_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_1337_);
                                crate::leanh::lean_dec(v___x_1336_);
                                v___x_1339_ = crate::leanh::lean_box(0);
                                v_isShared_1340_ = v_isSharedCheck_1344_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1336_);
                            v___x_1345_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7);
                            v___x_1346_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v___x_1345_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
                            if crate::leanh::lean_obj_tag(v___x_1346_) == 0 {
                                v_a_1347_ = crate::leanh::lean_ctor_get(v___x_1346_, 0);
                                v_isSharedCheck_1355_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1346_)) as u8;
                                if v_isSharedCheck_1355_ == 0 {
                                    v___x_1349_ = v___x_1346_;
                                    v_isShared_1350_ = v_isSharedCheck_1355_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1347_);
                                    crate::leanh::lean_dec(v___x_1346_);
                                    v___x_1349_ = crate::leanh::lean_box(0);
                                    v_isShared_1350_ = v_isSharedCheck_1355_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_1316_);
                                v_a_1356_ = crate::leanh::lean_ctor_get(v___x_1346_, 0);
                                v_isSharedCheck_1363_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1346_)) as u8;
                                if v_isSharedCheck_1363_ == 0 {
                                    v___x_1358_ = v___x_1346_;
                                    v_isShared_1359_ = v_isSharedCheck_1363_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1356_);
                                    crate::leanh::lean_dec(v___x_1346_);
                                    v___x_1358_ = crate::leanh::lean_box(0);
                                    v_isShared_1359_ = v_isSharedCheck_1363_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1334_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1333_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1323_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
                v___x_1324_ = 0;
                v___x_1325_ = l_Lean_MessageData_ofConstName(v_constName_1316_, v___x_1324_);
                v___x_1326_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1326_, 0, v___x_1323_);
                crate::leanh::lean_ctor_set(v___x_1326_, 1, v___x_1325_);
                v___x_1327_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3);
                v___x_1328_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1328_, 0, v___x_1326_);
                crate::leanh::lean_ctor_set(v___x_1328_, 1, v___x_1327_);
                v___x_1329_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_1328_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
                return v___x_1329_;
            }
            2 => {
                if v_isShared_1340_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1339_, 0);
                    v___x_1342_ = v___x_1339_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1343_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_val_1337_);
                    v___x_1342_ = v_reuseFailAlloc_1343_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1342_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_1347_) == 0 {
                    crate::leanh::lean_del_object(v___x_1349_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_1316_);
                    v_val_1351_ = crate::leanh::lean_ctor_get(v_a_1347_, 0);
                    crate::leanh::lean_inc(v_val_1351_);
                    crate::leanh::lean_dec_ref_known(v_a_1347_, 1);
                    if v_isShared_1350_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1349_, 0, v_val_1351_);
                        v___x_1353_ = v___x_1349_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1354_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_val_1351_);
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
                    v_reuseFailAlloc_1362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
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
    mut v_constName_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v___y_1366_: *mut crate::leanh::LeanObject,
    mut v___y_1367_: *mut crate::leanh::LeanObject,
    mut v___y_1368_: *mut crate::leanh::LeanObject,
    mut v___y_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1370_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(
        v_constName_1364_,
        v___y_1365_,
        v___y_1366_,
        v___y_1367_,
        v___y_1368_,
    );
    crate::leanh::lean_dec(v___y_1368_);
    crate::leanh::lean_dec_ref(v___y_1367_);
    crate::leanh::lean_dec(v___y_1366_);
    crate::leanh::lean_dec_ref(v___y_1365_);
    return v_res_1370_;
}
pub unsafe fn l_Lean_Meta_occursInCtorTypeMask(
    mut v_ctorName_1372_: *mut crate::leanh::LeanObject,
    mut v_a_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
    mut v_a_1375_: *mut crate::leanh::LeanObject,
    mut v_a_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1392_: u8 = 0;
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_1378_) == 0 {
                    v_a_1379_ = crate::leanh::lean_ctor_get(v___x_1378_, 0);
                    crate::leanh::lean_inc(v_a_1379_);
                    crate::leanh::lean_dec_ref_known(v___x_1378_, 1);
                    v_toConstantVal_1380_ = crate::leanh::lean_ctor_get(v_a_1379_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_1380_);
                    v_numParams_1381_ = crate::leanh::lean_ctor_get(v_a_1379_, 3);
                    crate::leanh::lean_inc(v_numParams_1381_);
                    v_numFields_1382_ = crate::leanh::lean_ctor_get(v_a_1379_, 4);
                    crate::leanh::lean_inc(v_numFields_1382_);
                    crate::leanh::lean_dec(v_a_1379_);
                    v_type_1383_ = crate::leanh::lean_ctor_get(v_toConstantVal_1380_, 2);
                    crate::leanh::lean_inc_ref(v_type_1383_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_1380_);
                    v___f_1384_ = l_Lean_Meta_occursInCtorTypeMask___closed__0;
                    v___f_1385_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1385_, 0, v_numFields_1382_);
                    crate::leanh::lean_closure_set(v___f_1385_, 1, v___f_1384_);
                    v___x_1386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1386_, 0, v_numParams_1381_);
                    v___x_1387_ = 0;
                    v___x_1388_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_1383_, v___x_1386_, v___f_1385_, v___x_1387_, v___x_1387_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
                    return v___x_1388_;
                } else {
                    v_a_1389_ = crate::leanh::lean_ctor_get(v___x_1378_, 0);
                    v_isSharedCheck_1396_ = (!crate::leanh::lean_is_exclusive(v___x_1378_)) as u8;
                    if v_isSharedCheck_1396_ == 0 {
                        v___x_1391_ = v___x_1378_;
                        v_isShared_1392_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1389_);
                        crate::leanh::lean_dec(v___x_1378_);
                        v___x_1391_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
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
    mut v_ctorName_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lean_Meta_occursInCtorTypeMask(
        v_ctorName_1397_,
        v_a_1398_,
        v_a_1399_,
        v_a_1400_,
        v_a_1401_,
    );
    crate::leanh::lean_dec(v_a_1401_);
    crate::leanh::lean_dec_ref(v_a_1400_);
    crate::leanh::lean_dec(v_a_1399_);
    crate::leanh::lean_dec_ref(v_a_1398_);
    return v_res_1403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(
    mut v_00_u03b1_1404_: *mut crate::leanh::LeanObject,
    mut v_msg_1405_: *mut crate::leanh::LeanObject,
    mut v___y_1406_: *mut crate::leanh::LeanObject,
    mut v___y_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
    return v___x_1411_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___boxed(
    mut v_00_u03b1_1412_: *mut crate::leanh::LeanObject,
    mut v_msg_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1419_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(v_00_u03b1_1412_, v_msg_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
    crate::leanh::lean_dec(v___y_1417_);
    crate::leanh::lean_dec_ref(v___y_1416_);
    crate::leanh::lean_dec(v___y_1415_);
    crate::leanh::lean_dec_ref(v___y_1414_);
    return v_res_1419_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(
    mut v_msg_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685__overap_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1427_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0;
    v___x_685__overap_1428_ = lean_panic_fn_borrowed(v___f_1427_, v_msg_1421_);
    crate::leanh::lean_inc(v___y_1425_);
    crate::leanh::lean_inc_ref(v___y_1424_);
    crate::leanh::lean_inc(v___y_1423_);
    crate::leanh::lean_inc_ref(v___y_1422_);
    v___x_1429_ = crate::leanh::lean_apply_5(
        v___x_685__overap_1428_,
        v___y_1422_,
        v___y_1423_,
        v___y_1424_,
        v___y_1425_,
        crate::leanh::lean_box(0),
    );
    return v___x_1429_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___boxed(
    mut v_msg_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1436_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
    crate::leanh::lean_dec(v___y_1434_);
    crate::leanh::lean_dec_ref(v___y_1433_);
    crate::leanh::lean_dec(v___y_1432_);
    crate::leanh::lean_dec_ref(v___y_1431_);
    return v_res_1436_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(
    mut v_00_u03b1_1437_: *mut crate::leanh::LeanObject,
    mut v_msg_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
    mut v___y_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1444_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
    return v___x_1444_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___boxed(
    mut v_00_u03b1_1445_: *mut crate::leanh::LeanObject,
    mut v_msg_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(v_00_u03b1_1445_, v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
    crate::leanh::lean_dec(v___y_1450_);
    crate::leanh::lean_dec_ref(v___y_1449_);
    crate::leanh::lean_dec(v___y_1448_);
    crate::leanh::lean_dec_ref(v___y_1447_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(
    mut v_k_1453_: *mut crate::leanh::LeanObject,
    mut v_b_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1458_);
    crate::leanh::lean_inc_ref(v___y_1457_);
    crate::leanh::lean_inc(v___y_1456_);
    crate::leanh::lean_inc_ref(v___y_1455_);
    v___x_1460_ = crate::leanh::lean_apply_6(
        v_k_1453_,
        v_b_1454_,
        v___y_1455_,
        v___y_1456_,
        v___y_1457_,
        v___y_1458_,
        crate::leanh::lean_box(0),
    );
    return v___x_1460_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed(
    mut v_k_1461_: *mut crate::leanh::LeanObject,
    mut v_b_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
    mut v___y_1465_: *mut crate::leanh::LeanObject,
    mut v___y_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1468_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(v_k_1461_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
    crate::leanh::lean_dec(v___y_1466_);
    crate::leanh::lean_dec_ref(v___y_1465_);
    crate::leanh::lean_dec(v___y_1464_);
    crate::leanh::lean_dec_ref(v___y_1463_);
    return v_res_1468_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(
    mut v_name_1469_: *mut crate::leanh::LeanObject,
    mut v_bi_1470_: u8,
    mut v_type_1471_: *mut crate::leanh::LeanObject,
    mut v_k_1472_: *mut crate::leanh::LeanObject,
    mut v_kind_1473_: u8,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_a_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1479_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_1479_, 0, v_k_1472_);
                v___x_1480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
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
                if crate::leanh::lean_obj_tag(v___x_1480_) == 0 {
                    v_a_1481_ = crate::leanh::lean_ctor_get(v___x_1480_, 0);
                    v_isSharedCheck_1488_ = (!crate::leanh::lean_is_exclusive(v___x_1480_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1483_ = v___x_1480_;
                        v_isShared_1484_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1481_);
                        crate::leanh::lean_dec(v___x_1480_);
                        v___x_1483_ = crate::leanh::lean_box(0);
                        v_isShared_1484_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1489_ = crate::leanh::lean_ctor_get(v___x_1480_, 0);
                    v_isSharedCheck_1496_ = (!crate::leanh::lean_is_exclusive(v___x_1480_)) as u8;
                    if v_isSharedCheck_1496_ == 0 {
                        v___x_1491_ = v___x_1480_;
                        v_isShared_1492_ = v_isSharedCheck_1496_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1489_);
                        crate::leanh::lean_dec(v___x_1480_);
                        v___x_1491_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
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
                    v_reuseFailAlloc_1495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
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
    mut v_name_1497_: *mut crate::leanh::LeanObject,
    mut v_bi_1498_: *mut crate::leanh::LeanObject,
    mut v_type_1499_: *mut crate::leanh::LeanObject,
    mut v_k_1500_: *mut crate::leanh::LeanObject,
    mut v_kind_1501_: *mut crate::leanh::LeanObject,
    mut v___y_1502_: *mut crate::leanh::LeanObject,
    mut v___y_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_1507_: u8 = 0;
    let mut v_kind_boxed_1508_: u8 = 0;
    let mut v_res_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1507_ = (crate::leanh::lean_unbox(v_bi_1498_) as u8);
    v_kind_boxed_1508_ = (crate::leanh::lean_unbox(v_kind_1501_) as u8);
    v_res_1509_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_1497_, v_bi_boxed_1507_, v_type_1499_, v_k_1500_, v_kind_boxed_1508_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
    crate::leanh::lean_dec(v___y_1505_);
    crate::leanh::lean_dec_ref(v___y_1504_);
    crate::leanh::lean_dec(v___y_1503_);
    crate::leanh::lean_dec_ref(v___y_1502_);
    return v_res_1509_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(
    mut v_name_1510_: *mut crate::leanh::LeanObject,
    mut v_type_1511_: *mut crate::leanh::LeanObject,
    mut v_k_1512_: *mut crate::leanh::LeanObject,
    mut v___y_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
    mut v___y_1515_: *mut crate::leanh::LeanObject,
    mut v___y_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: u8 = 0;
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = 0;
    v___x_1519_ = 0;
    v___x_1520_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_1510_, v___x_1518_, v_type_1511_, v_k_1512_, v___x_1519_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
    return v___x_1520_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg___boxed(
    mut v_name_1521_: *mut crate::leanh::LeanObject,
    mut v_type_1522_: *mut crate::leanh::LeanObject,
    mut v_k_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
    mut v___y_1526_: *mut crate::leanh::LeanObject,
    mut v___y_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_1521_, v_type_1522_, v_k_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
    crate::leanh::lean_dec(v___y_1527_);
    crate::leanh::lean_dec_ref(v___y_1526_);
    crate::leanh::lean_dec(v___y_1525_);
    crate::leanh::lean_dec_ref(v___y_1524_);
    return v_res_1529_;
}
pub unsafe fn _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2;
    v___x_1534_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_1535_ = crate::leanh::lean_unsigned_to_nat(91);
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
    mut v_zs2_1539_: *mut crate::leanh::LeanObject,
    mut v_acc_1540_: *mut crate::leanh::LeanObject,
    mut v_ctor_1541_: *mut crate::leanh::LeanObject,
    mut v_k_1542_: *mut crate::leanh::LeanObject,
    mut v_zs_1543_: *mut crate::leanh::LeanObject,
    mut v_indices_1544_: *mut crate::leanh::LeanObject,
    mut v_tail_1545_: *mut crate::leanh::LeanObject,
    mut v_tail_1546_: *mut crate::leanh::LeanObject,
    mut v_z_x27_1547_: *mut crate::leanh::LeanObject,
    mut v___y_1548_: *mut crate::leanh::LeanObject,
    mut v___y_1549_: *mut crate::leanh::LeanObject,
    mut v___y_1550_: *mut crate::leanh::LeanObject,
    mut v___y_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1551_);
    crate::leanh::lean_dec_ref(v___y_1550_);
    crate::leanh::lean_dec(v___y_1549_);
    crate::leanh::lean_dec_ref(v___y_1548_);
    return v_res_1553_;
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(
    mut v_ctor_1555_: *mut crate::leanh::LeanObject,
    mut v_k_1556_: *mut crate::leanh::LeanObject,
    mut v_zs_1557_: *mut crate::leanh::LeanObject,
    mut v_indices_1558_: *mut crate::leanh::LeanObject,
    mut v_zs2_1559_: *mut crate::leanh::LeanObject,
    mut v_mask_1560_: *mut crate::leanh::LeanObject,
    mut v_todo_1561_: *mut crate::leanh::LeanObject,
    mut v_acc_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v_tail_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u8 = 0;
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1589_: u8 = 0;
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut v_a_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_mask_1560_) == 1 {
                    v_head_1568_ = crate::leanh::lean_ctor_get(v_mask_1560_, 0);
                    v___x_1569_ = (crate::leanh::lean_unbox(v_head_1568_) as u8);
                    if v___x_1569_ == 0 {
                        if crate::leanh::lean_obj_tag(v_todo_1561_) == 1 {
                            v_tail_1570_ = crate::leanh::lean_ctor_get(v_mask_1560_, 1);
                            crate::leanh::lean_inc(v_tail_1570_);
                            crate::leanh::lean_dec_ref_known(v_mask_1560_, 2);
                            v_tail_1571_ = crate::leanh::lean_ctor_get(v_todo_1561_, 1);
                            crate::leanh::lean_inc(v_tail_1571_);
                            crate::leanh::lean_dec_ref_known(v_todo_1561_, 2);
                            crate::leanh::lean_inc_ref(v_ctor_1555_);
                            v___x_1572_ = l_Lean_mkAppN(v_ctor_1555_, v_zs2_1559_);
                            crate::leanh::lean_inc(v_a_1566_);
                            crate::leanh::lean_inc_ref(v_a_1565_);
                            crate::leanh::lean_inc(v_a_1564_);
                            crate::leanh::lean_inc_ref(v_a_1563_);
                            v___x_1573_ = lean_infer_type(
                                v___x_1572_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1573_) == 0 {
                                v_a_1574_ = crate::leanh::lean_ctor_get(v___x_1573_, 0);
                                crate::leanh::lean_inc(v_a_1574_);
                                crate::leanh::lean_dec_ref_known(v___x_1573_, 1);
                                v___x_1575_ = l_Lean_Meta_whnfForall(
                                    v_a_1574_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1575_) == 0 {
                                    v_a_1576_ = crate::leanh::lean_ctor_get(v___x_1575_, 0);
                                    crate::leanh::lean_inc(v_a_1576_);
                                    crate::leanh::lean_dec_ref_known(v___x_1575_, 1);
                                    v___x_1577_ = l_Lean_Expr_isForall(v_a_1576_);
                                    if v___x_1577_ == 0 {
                                        crate::leanh::lean_dec(v_a_1576_);
                                        crate::leanh::lean_dec(v_tail_1571_);
                                        crate::leanh::lean_dec(v_tail_1570_);
                                        crate::leanh::lean_dec_ref(v_acc_1562_);
                                        crate::leanh::lean_dec_ref(v_zs2_1559_);
                                        crate::leanh::lean_dec_ref(v_indices_1558_);
                                        crate::leanh::lean_dec_ref(v_zs_1557_);
                                        crate::leanh::lean_dec_ref(v_k_1556_);
                                        crate::leanh::lean_dec_ref(v_ctor_1555_);
                                        v___x_1578_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once), _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3);
                                        v___x_1579_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v___x_1578_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
                                        return v___x_1579_;
                                    } else {
                                        v___f_1580_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 8);
                                        crate::leanh::lean_closure_set(v___f_1580_, 0, v_zs2_1559_);
                                        crate::leanh::lean_closure_set(v___f_1580_, 1, v_acc_1562_);
                                        crate::leanh::lean_closure_set(
                                            v___f_1580_,
                                            2,
                                            v_ctor_1555_,
                                        );
                                        crate::leanh::lean_closure_set(v___f_1580_, 3, v_k_1556_);
                                        crate::leanh::lean_closure_set(v___f_1580_, 4, v_zs_1557_);
                                        crate::leanh::lean_closure_set(
                                            v___f_1580_,
                                            5,
                                            v_indices_1558_,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1580_,
                                            6,
                                            v_tail_1570_,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1580_,
                                            7,
                                            v_tail_1571_,
                                        );
                                        v___x_1581_ = l_Lean_Expr_bindingName_x21(v_a_1576_);
                                        v___x_1582_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4;
                                        v___x_1583_ =
                                            lean_name_append_after(v___x_1581_, v___x_1582_);
                                        v___x_1584_ = l_Lean_Expr_bindingDomain_x21(v_a_1576_);
                                        crate::leanh::lean_dec(v_a_1576_);
                                        v___x_1585_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v___x_1583_, v___x_1584_, v___f_1580_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
                                        return v___x_1585_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_tail_1571_);
                                    crate::leanh::lean_dec(v_tail_1570_);
                                    crate::leanh::lean_dec_ref(v_acc_1562_);
                                    crate::leanh::lean_dec_ref(v_zs2_1559_);
                                    crate::leanh::lean_dec_ref(v_indices_1558_);
                                    crate::leanh::lean_dec_ref(v_zs_1557_);
                                    crate::leanh::lean_dec_ref(v_k_1556_);
                                    crate::leanh::lean_dec_ref(v_ctor_1555_);
                                    v_a_1586_ = crate::leanh::lean_ctor_get(v___x_1575_, 0);
                                    v_isSharedCheck_1593_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1575_)) as u8;
                                    if v_isSharedCheck_1593_ == 0 {
                                        v___x_1588_ = v___x_1575_;
                                        v_isShared_1589_ = v_isSharedCheck_1593_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1586_);
                                        crate::leanh::lean_dec(v___x_1575_);
                                        v___x_1588_ = crate::leanh::lean_box(0);
                                        v_isShared_1589_ = v_isSharedCheck_1593_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_tail_1571_);
                                crate::leanh::lean_dec(v_tail_1570_);
                                crate::leanh::lean_dec_ref(v_acc_1562_);
                                crate::leanh::lean_dec_ref(v_zs2_1559_);
                                crate::leanh::lean_dec_ref(v_indices_1558_);
                                crate::leanh::lean_dec_ref(v_zs_1557_);
                                crate::leanh::lean_dec_ref(v_k_1556_);
                                crate::leanh::lean_dec_ref(v_ctor_1555_);
                                v_a_1594_ = crate::leanh::lean_ctor_get(v___x_1573_, 0);
                                v_isSharedCheck_1601_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1573_)) as u8;
                                if v_isSharedCheck_1601_ == 0 {
                                    v___x_1596_ = v___x_1573_;
                                    v_isShared_1597_ = v_isSharedCheck_1601_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1594_);
                                    crate::leanh::lean_dec(v___x_1573_);
                                    v___x_1596_ = crate::leanh::lean_box(0);
                                    v_isShared_1597_ = v_isSharedCheck_1601_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_mask_1560_, 2);
                            crate::leanh::lean_dec(v_todo_1561_);
                            crate::leanh::lean_dec_ref(v_ctor_1555_);
                            crate::leanh::lean_inc(v_a_1566_);
                            crate::leanh::lean_inc_ref(v_a_1565_);
                            crate::leanh::lean_inc(v_a_1564_);
                            crate::leanh::lean_inc_ref(v_a_1563_);
                            v___x_1602_ = crate::leanh::lean_apply_9(
                                v_k_1556_,
                                v_acc_1562_,
                                v_indices_1558_,
                                v_zs_1557_,
                                v_zs2_1559_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_1602_;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_todo_1561_) == 1 {
                            v_tail_1603_ = crate::leanh::lean_ctor_get(v_mask_1560_, 1);
                            crate::leanh::lean_inc(v_tail_1603_);
                            crate::leanh::lean_dec_ref_known(v_mask_1560_, 2);
                            v_head_1604_ = crate::leanh::lean_ctor_get(v_todo_1561_, 0);
                            crate::leanh::lean_inc(v_head_1604_);
                            v_tail_1605_ = crate::leanh::lean_ctor_get(v_todo_1561_, 1);
                            crate::leanh::lean_inc(v_tail_1605_);
                            crate::leanh::lean_dec_ref_known(v_todo_1561_, 2);
                            v___x_1606_ = lean_array_push(v_zs2_1559_, v_head_1604_);
                            v_zs2_1559_ = v___x_1606_;
                            v_mask_1560_ = v_tail_1603_;
                            v_todo_1561_ = v_tail_1605_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_mask_1560_, 2);
                            crate::leanh::lean_dec(v_todo_1561_);
                            crate::leanh::lean_dec_ref(v_ctor_1555_);
                            crate::leanh::lean_inc(v_a_1566_);
                            crate::leanh::lean_inc_ref(v_a_1565_);
                            crate::leanh::lean_inc(v_a_1564_);
                            crate::leanh::lean_inc_ref(v_a_1563_);
                            v___x_1608_ = crate::leanh::lean_apply_9(
                                v_k_1556_,
                                v_acc_1562_,
                                v_indices_1558_,
                                v_zs_1557_,
                                v_zs2_1559_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_1608_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_todo_1561_);
                    crate::leanh::lean_dec(v_mask_1560_);
                    crate::leanh::lean_dec_ref(v_ctor_1555_);
                    crate::leanh::lean_inc(v_a_1566_);
                    crate::leanh::lean_inc_ref(v_a_1565_);
                    crate::leanh::lean_inc(v_a_1564_);
                    crate::leanh::lean_inc_ref(v_a_1563_);
                    v___x_1609_ = crate::leanh::lean_apply_9(
                        v_k_1556_,
                        v_acc_1562_,
                        v_indices_1558_,
                        v_zs_1557_,
                        v_zs2_1559_,
                        v_a_1563_,
                        v_a_1564_,
                        v_a_1565_,
                        v_a_1566_,
                        crate::leanh::lean_box(0),
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
                    v_reuseFailAlloc_1592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
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
                    v_reuseFailAlloc_1600_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
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
    mut v_zs2_1610_: *mut crate::leanh::LeanObject,
    mut v_acc_1611_: *mut crate::leanh::LeanObject,
    mut v_ctor_1612_: *mut crate::leanh::LeanObject,
    mut v_k_1613_: *mut crate::leanh::LeanObject,
    mut v_zs_1614_: *mut crate::leanh::LeanObject,
    mut v_indices_1615_: *mut crate::leanh::LeanObject,
    mut v_tail_1616_: *mut crate::leanh::LeanObject,
    mut v_tail_1617_: *mut crate::leanh::LeanObject,
    mut v_z_x27_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_z_x27_1618_);
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
    mut v_ctor_1627_: *mut crate::leanh::LeanObject,
    mut v_k_1628_: *mut crate::leanh::LeanObject,
    mut v_zs_1629_: *mut crate::leanh::LeanObject,
    mut v_indices_1630_: *mut crate::leanh::LeanObject,
    mut v_zs2_1631_: *mut crate::leanh::LeanObject,
    mut v_mask_1632_: *mut crate::leanh::LeanObject,
    mut v_todo_1633_: *mut crate::leanh::LeanObject,
    mut v_acc_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
    mut v_a_1637_: *mut crate::leanh::LeanObject,
    mut v_a_1638_: *mut crate::leanh::LeanObject,
    mut v_a_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1638_);
    crate::leanh::lean_dec_ref(v_a_1637_);
    crate::leanh::lean_dec(v_a_1636_);
    crate::leanh::lean_dec_ref(v_a_1635_);
    return v_res_1640_;
}
pub unsafe fn l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(
    mut v_00_u03b1_1641_: *mut crate::leanh::LeanObject,
    mut v_ctor_1642_: *mut crate::leanh::LeanObject,
    mut v_k_1643_: *mut crate::leanh::LeanObject,
    mut v_zs_1644_: *mut crate::leanh::LeanObject,
    mut v_indices_1645_: *mut crate::leanh::LeanObject,
    mut v_zs2_1646_: *mut crate::leanh::LeanObject,
    mut v_mask_1647_: *mut crate::leanh::LeanObject,
    mut v_todo_1648_: *mut crate::leanh::LeanObject,
    mut v_acc_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1656_: *mut crate::leanh::LeanObject,
    mut v_ctor_1657_: *mut crate::leanh::LeanObject,
    mut v_k_1658_: *mut crate::leanh::LeanObject,
    mut v_zs_1659_: *mut crate::leanh::LeanObject,
    mut v_indices_1660_: *mut crate::leanh::LeanObject,
    mut v_zs2_1661_: *mut crate::leanh::LeanObject,
    mut v_mask_1662_: *mut crate::leanh::LeanObject,
    mut v_todo_1663_: *mut crate::leanh::LeanObject,
    mut v_acc_1664_: *mut crate::leanh::LeanObject,
    mut v_a_1665_: *mut crate::leanh::LeanObject,
    mut v_a_1666_: *mut crate::leanh::LeanObject,
    mut v_a_1667_: *mut crate::leanh::LeanObject,
    mut v_a_1668_: *mut crate::leanh::LeanObject,
    mut v_a_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1668_);
    crate::leanh::lean_dec_ref(v_a_1667_);
    crate::leanh::lean_dec(v_a_1666_);
    crate::leanh::lean_dec_ref(v_a_1665_);
    return v_res_1670_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(
    mut v_00_u03b1_1671_: *mut crate::leanh::LeanObject,
    mut v_name_1672_: *mut crate::leanh::LeanObject,
    mut v_bi_1673_: u8,
    mut v_type_1674_: *mut crate::leanh::LeanObject,
    mut v_k_1675_: *mut crate::leanh::LeanObject,
    mut v_kind_1676_: u8,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1682_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_1672_, v_bi_1673_, v_type_1674_, v_k_1675_, v_kind_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
    return v___x_1682_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___boxed(
    mut v_00_u03b1_1683_: *mut crate::leanh::LeanObject,
    mut v_name_1684_: *mut crate::leanh::LeanObject,
    mut v_bi_1685_: *mut crate::leanh::LeanObject,
    mut v_type_1686_: *mut crate::leanh::LeanObject,
    mut v_k_1687_: *mut crate::leanh::LeanObject,
    mut v_kind_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
    mut v___y_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_1694_: u8 = 0;
    let mut v_kind_boxed_1695_: u8 = 0;
    let mut v_res_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1694_ = (crate::leanh::lean_unbox(v_bi_1685_) as u8);
    v_kind_boxed_1695_ = (crate::leanh::lean_unbox(v_kind_1688_) as u8);
    v_res_1696_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(v_00_u03b1_1683_, v_name_1684_, v_bi_boxed_1694_, v_type_1686_, v_k_1687_, v_kind_boxed_1695_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
    crate::leanh::lean_dec(v___y_1692_);
    crate::leanh::lean_dec_ref(v___y_1691_);
    crate::leanh::lean_dec(v___y_1690_);
    crate::leanh::lean_dec_ref(v___y_1689_);
    return v_res_1696_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(
    mut v_00_u03b1_1697_: *mut crate::leanh::LeanObject,
    mut v_name_1698_: *mut crate::leanh::LeanObject,
    mut v_type_1699_: *mut crate::leanh::LeanObject,
    mut v_k_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_1698_, v_type_1699_, v_k_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___boxed(
    mut v_00_u03b1_1707_: *mut crate::leanh::LeanObject,
    mut v_name_1708_: *mut crate::leanh::LeanObject,
    mut v_type_1709_: *mut crate::leanh::LeanObject,
    mut v_k_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1716_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(v_00_u03b1_1707_, v_name_1708_, v_type_1709_, v_k_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
    crate::leanh::lean_dec(v___y_1714_);
    crate::leanh::lean_dec_ref(v___y_1713_);
    crate::leanh::lean_dec(v___y_1712_);
    crate::leanh::lean_dec_ref(v___y_1711_);
    return v_res_1716_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(
    mut v_type_1717_: *mut crate::leanh::LeanObject,
    mut v_k_1718_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1719_: u8,
    mut v_whnfType_1720_: u8,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
    mut v___y_1722_: *mut crate::leanh::LeanObject,
    mut v___y_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut v_a_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1726_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1726_, 0, v_k_1718_);
                v___x_1727_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_1717_,
                    v___f_1726_,
                    v_cleanupAnnotations_1719_,
                    v_whnfType_1720_,
                    v___y_1721_,
                    v___y_1722_,
                    v___y_1723_,
                    v___y_1724_,
                );
                if crate::leanh::lean_obj_tag(v___x_1727_) == 0 {
                    v_a_1728_ = crate::leanh::lean_ctor_get(v___x_1727_, 0);
                    v_isSharedCheck_1735_ = (!crate::leanh::lean_is_exclusive(v___x_1727_)) as u8;
                    if v_isSharedCheck_1735_ == 0 {
                        v___x_1730_ = v___x_1727_;
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1728_);
                        crate::leanh::lean_dec(v___x_1727_);
                        v___x_1730_ = crate::leanh::lean_box(0);
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1736_ = crate::leanh::lean_ctor_get(v___x_1727_, 0);
                    v_isSharedCheck_1743_ = (!crate::leanh::lean_is_exclusive(v___x_1727_)) as u8;
                    if v_isSharedCheck_1743_ == 0 {
                        v___x_1738_ = v___x_1727_;
                        v_isShared_1739_ = v_isSharedCheck_1743_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1736_);
                        crate::leanh::lean_dec(v___x_1727_);
                        v___x_1738_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1734_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
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
                    v_reuseFailAlloc_1742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
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
    mut v_type_1744_: *mut crate::leanh::LeanObject,
    mut v_k_1745_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1746_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1747_: *mut crate::leanh::LeanObject,
    mut v___y_1748_: *mut crate::leanh::LeanObject,
    mut v___y_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1753_: u8 = 0;
    let mut v_whnfType_boxed_1754_: u8 = 0;
    let mut v_res_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1753_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1746_) as u8);
    v_whnfType_boxed_1754_ = (crate::leanh::lean_unbox(v_whnfType_1747_) as u8);
    v_res_1755_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_1744_, v_k_1745_, v_cleanupAnnotations_boxed_1753_, v_whnfType_boxed_1754_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
    crate::leanh::lean_dec(v___y_1751_);
    crate::leanh::lean_dec_ref(v___y_1750_);
    crate::leanh::lean_dec(v___y_1749_);
    crate::leanh::lean_dec_ref(v___y_1748_);
    return v_res_1755_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(
    mut v_00_u03b1_1756_: *mut crate::leanh::LeanObject,
    mut v_type_1757_: *mut crate::leanh::LeanObject,
    mut v_k_1758_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1759_: u8,
    mut v_whnfType_1760_: u8,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
    mut v___y_1763_: *mut crate::leanh::LeanObject,
    mut v___y_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1766_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_1757_, v_k_1758_, v_cleanupAnnotations_1759_, v_whnfType_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
    return v___x_1766_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___boxed(
    mut v_00_u03b1_1767_: *mut crate::leanh::LeanObject,
    mut v_type_1768_: *mut crate::leanh::LeanObject,
    mut v_k_1769_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1770_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1771_: *mut crate::leanh::LeanObject,
    mut v___y_1772_: *mut crate::leanh::LeanObject,
    mut v___y_1773_: *mut crate::leanh::LeanObject,
    mut v___y_1774_: *mut crate::leanh::LeanObject,
    mut v___y_1775_: *mut crate::leanh::LeanObject,
    mut v___y_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1777_: u8 = 0;
    let mut v_whnfType_boxed_1778_: u8 = 0;
    let mut v_res_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1777_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1770_) as u8);
    v_whnfType_boxed_1778_ = (crate::leanh::lean_unbox(v_whnfType_1771_) as u8);
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
    crate::leanh::lean_dec(v___y_1775_);
    crate::leanh::lean_dec_ref(v___y_1774_);
    crate::leanh::lean_dec(v___y_1773_);
    crate::leanh::lean_dec_ref(v___y_1772_);
    return v_res_1779_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ =
        l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0;
    v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
    return v___x_1782_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(
    mut v_constName_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
    mut v___y_1785_: *mut crate::leanh::LeanObject,
    mut v___y_1786_: *mut crate::leanh::LeanObject,
    mut v___y_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1789_ = lean_st_ref_get(v___y_1787_);
                v_env_1790_ = crate::leanh::lean_ctor_get(v___x_1789_, 0);
                crate::leanh::lean_inc_ref(v_env_1790_);
                crate::leanh::lean_dec(v___x_1789_);
                crate::leanh::lean_inc(v_constName_1783_);
                v___x_1791_ = l_Lean_isInductiveCore_x3f(v_env_1790_, v_constName_1783_);
                if crate::leanh::lean_obj_tag(v___x_1791_) == 0 {
                    v___x_1792_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
                    v___x_1793_ = 0;
                    v___x_1794_ = l_Lean_MessageData_ofConstName(v_constName_1783_, v___x_1793_);
                    v___x_1795_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1795_, 0, v___x_1792_);
                    crate::leanh::lean_ctor_set(v___x_1795_, 1, v___x_1794_);
                    v___x_1796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1);
                    v___x_1797_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1797_, 0, v___x_1795_);
                    crate::leanh::lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                    v___x_1798_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_1797_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
                    return v___x_1798_;
                } else {
                    crate::leanh::lean_dec(v_constName_1783_);
                    v_val_1799_ = crate::leanh::lean_ctor_get(v___x_1791_, 0);
                    v_isSharedCheck_1806_ = (!crate::leanh::lean_is_exclusive(v___x_1791_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v___x_1801_ = v___x_1791_;
                        v_isShared_1802_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1799_);
                        crate::leanh::lean_dec(v___x_1791_);
                        v___x_1801_ = crate::leanh::lean_box(0);
                        v_isShared_1802_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1802_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1801_, 0);
                    v___x_1804_ = v___x_1801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_val_1799_);
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
    mut v_constName_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(
        v_constName_1807_,
        v___y_1808_,
        v___y_1809_,
        v___y_1810_,
        v___y_1811_,
    );
    crate::leanh::lean_dec(v___y_1811_);
    crate::leanh::lean_dec_ref(v___y_1810_);
    crate::leanh::lean_dec(v___y_1809_);
    crate::leanh::lean_dec_ref(v___y_1808_);
    return v_res_1813_;
}
pub unsafe fn _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = crate::leanh::lean_box(0);
    v_dummy_1815_ = l_Lean_Expr_sort___override(v___x_1814_);
    return v_dummy_1815_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(
    mut v_ctor_1818_: *mut crate::leanh::LeanObject,
    mut v_k_1819_: *mut crate::leanh::LeanObject,
    mut v_zs_1820_: *mut crate::leanh::LeanObject,
    mut v_ctorRet_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1854_: u8 = 0;
    let mut v_a_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_a_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_a_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1825_);
                crate::leanh::lean_inc_ref(v___y_1824_);
                crate::leanh::lean_inc(v___y_1823_);
                crate::leanh::lean_inc_ref(v___y_1822_);
                v___x_1827_ = lean_whnf(
                    v_ctorRet_1821_,
                    v___y_1822_,
                    v___y_1823_,
                    v___y_1824_,
                    v___y_1825_,
                );
                if crate::leanh::lean_obj_tag(v___x_1827_) == 0 {
                    v_a_1828_ = crate::leanh::lean_ctor_get(v___x_1827_, 0);
                    crate::leanh::lean_inc(v_a_1828_);
                    crate::leanh::lean_dec_ref_known(v___x_1827_, 1);
                    v___x_1829_ = l_Lean_Core_betaReduce(v_a_1828_, v___y_1824_, v___y_1825_);
                    if crate::leanh::lean_obj_tag(v___x_1829_) == 0 {
                        v_a_1830_ = crate::leanh::lean_ctor_get(v___x_1829_, 0);
                        crate::leanh::lean_inc(v_a_1830_);
                        crate::leanh::lean_dec_ref_known(v___x_1829_, 1);
                        v___x_1831_ = l_Lean_Expr_getAppFn(v_a_1830_);
                        v___x_1832_ = l_Lean_Expr_constName_x21(v___x_1831_);
                        crate::leanh::lean_dec_ref(v___x_1831_);
                        v___x_1833_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v___x_1832_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
                        if crate::leanh::lean_obj_tag(v___x_1833_) == 0 {
                            v_a_1834_ = crate::leanh::lean_ctor_get(v___x_1833_, 0);
                            crate::leanh::lean_inc(v_a_1834_);
                            crate::leanh::lean_dec_ref_known(v___x_1833_, 1);
                            v_numIndices_1835_ = crate::leanh::lean_ctor_get(v_a_1834_, 2);
                            crate::leanh::lean_inc(v_numIndices_1835_);
                            crate::leanh::lean_dec(v_a_1834_);
                            v___x_1836_ = l_Lean_Expr_getAppFn(v_ctor_1818_);
                            v___x_1837_ = l_Lean_Expr_constName_x21(v___x_1836_);
                            crate::leanh::lean_dec_ref(v___x_1836_);
                            v___x_1838_ = l_Lean_Meta_occursInCtorTypeMask(
                                v___x_1837_,
                                v___y_1822_,
                                v___y_1823_,
                                v___y_1824_,
                                v___y_1825_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1838_) == 0 {
                                v_a_1839_ = crate::leanh::lean_ctor_get(v___x_1838_, 0);
                                crate::leanh::lean_inc(v_a_1839_);
                                crate::leanh::lean_dec_ref_known(v___x_1838_, 1);
                                v_dummy_1840_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once), _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0);
                                crate::leanh::lean_inc(v_numIndices_1835_);
                                v___x_1841_ = lean_mk_array(v_numIndices_1835_, v_dummy_1840_);
                                v___x_1842_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(
                                    v_numIndices_1835_,
                                    v_a_1830_,
                                    v___x_1841_,
                                );
                                v___x_1843_ =
                                    l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1;
                                v___x_1844_ = lean_array_to_list(v_a_1839_);
                                crate::leanh::lean_inc_ref_n(v_zs_1820_, 2);
                                v___x_1845_ = lean_array_to_list(v_zs_1820_);
                                v___x_1846_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_1818_, v_k_1819_, v_zs_1820_, v___x_1842_, v___x_1843_, v___x_1844_, v___x_1845_, v_zs_1820_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
                                return v___x_1846_;
                            } else {
                                crate::leanh::lean_dec(v_numIndices_1835_);
                                crate::leanh::lean_dec(v_a_1830_);
                                crate::leanh::lean_dec_ref(v_zs_1820_);
                                crate::leanh::lean_dec_ref(v_k_1819_);
                                crate::leanh::lean_dec_ref(v_ctor_1818_);
                                v_a_1847_ = crate::leanh::lean_ctor_get(v___x_1838_, 0);
                                v_isSharedCheck_1854_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1838_)) as u8;
                                if v_isSharedCheck_1854_ == 0 {
                                    v___x_1849_ = v___x_1838_;
                                    v_isShared_1850_ = v_isSharedCheck_1854_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1847_);
                                    crate::leanh::lean_dec(v___x_1838_);
                                    v___x_1849_ = crate::leanh::lean_box(0);
                                    v_isShared_1850_ = v_isSharedCheck_1854_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1830_);
                            crate::leanh::lean_dec_ref(v_zs_1820_);
                            crate::leanh::lean_dec_ref(v_k_1819_);
                            crate::leanh::lean_dec_ref(v_ctor_1818_);
                            v_a_1855_ = crate::leanh::lean_ctor_get(v___x_1833_, 0);
                            v_isSharedCheck_1862_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1833_)) as u8;
                            if v_isSharedCheck_1862_ == 0 {
                                v___x_1857_ = v___x_1833_;
                                v_isShared_1858_ = v_isSharedCheck_1862_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1855_);
                                crate::leanh::lean_dec(v___x_1833_);
                                v___x_1857_ = crate::leanh::lean_box(0);
                                v_isShared_1858_ = v_isSharedCheck_1862_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_zs_1820_);
                        crate::leanh::lean_dec_ref(v_k_1819_);
                        crate::leanh::lean_dec_ref(v_ctor_1818_);
                        v_a_1863_ = crate::leanh::lean_ctor_get(v___x_1829_, 0);
                        v_isSharedCheck_1870_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1829_)) as u8;
                        if v_isSharedCheck_1870_ == 0 {
                            v___x_1865_ = v___x_1829_;
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1863_);
                            crate::leanh::lean_dec(v___x_1829_);
                            v___x_1865_ = crate::leanh::lean_box(0);
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_zs_1820_);
                    crate::leanh::lean_dec_ref(v_k_1819_);
                    crate::leanh::lean_dec_ref(v_ctor_1818_);
                    v_a_1871_ = crate::leanh::lean_ctor_get(v___x_1827_, 0);
                    v_isSharedCheck_1878_ = (!crate::leanh::lean_is_exclusive(v___x_1827_)) as u8;
                    if v_isSharedCheck_1878_ == 0 {
                        v___x_1873_ = v___x_1827_;
                        v_isShared_1874_ = v_isSharedCheck_1878_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1871_);
                        crate::leanh::lean_dec(v___x_1827_);
                        v___x_1873_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1853_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
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
                    v_reuseFailAlloc_1861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
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
                    v_reuseFailAlloc_1869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
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
                    v_reuseFailAlloc_1877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
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
    mut v_ctor_1879_: *mut crate::leanh::LeanObject,
    mut v_k_1880_: *mut crate::leanh::LeanObject,
    mut v_zs_1881_: *mut crate::leanh::LeanObject,
    mut v_ctorRet_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1886_);
    crate::leanh::lean_dec_ref(v___y_1885_);
    crate::leanh::lean_dec(v___y_1884_);
    crate::leanh::lean_dec_ref(v___y_1883_);
    return v_res_1888_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices___redArg(
    mut v_ctor_1889_: *mut crate::leanh::LeanObject,
    mut v_k_1890_: *mut crate::leanh::LeanObject,
    mut v_a_1891_: *mut crate::leanh::LeanObject,
    mut v_a_1892_: *mut crate::leanh::LeanObject,
    mut v_a_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: u8 = 0;
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1894_);
                crate::leanh::lean_inc_ref(v_a_1893_);
                crate::leanh::lean_inc(v_a_1892_);
                crate::leanh::lean_inc_ref(v_a_1891_);
                crate::leanh::lean_inc_ref(v_ctor_1889_);
                v___x_1896_ =
                    lean_infer_type(v_ctor_1889_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
                if crate::leanh::lean_obj_tag(v___x_1896_) == 0 {
                    v_a_1897_ = crate::leanh::lean_ctor_get(v___x_1896_, 0);
                    crate::leanh::lean_inc(v_a_1897_);
                    crate::leanh::lean_dec_ref_known(v___x_1896_, 1);
                    v___f_1898_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1898_, 0, v_ctor_1889_);
                    crate::leanh::lean_closure_set(v___f_1898_, 1, v_k_1890_);
                    v___x_1899_ = 0;
                    v___x_1900_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_a_1897_, v___f_1898_, v___x_1899_, v___x_1899_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
                    return v___x_1900_;
                } else {
                    crate::leanh::lean_dec_ref(v_k_1890_);
                    crate::leanh::lean_dec_ref(v_ctor_1889_);
                    v_a_1901_ = crate::leanh::lean_ctor_get(v___x_1896_, 0);
                    v_isSharedCheck_1908_ = (!crate::leanh::lean_is_exclusive(v___x_1896_)) as u8;
                    if v_isSharedCheck_1908_ == 0 {
                        v___x_1903_ = v___x_1896_;
                        v_isShared_1904_ = v_isSharedCheck_1908_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1901_);
                        crate::leanh::lean_dec(v___x_1896_);
                        v___x_1903_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
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
    mut v_ctor_1909_: *mut crate::leanh::LeanObject,
    mut v_k_1910_: *mut crate::leanh::LeanObject,
    mut v_a_1911_: *mut crate::leanh::LeanObject,
    mut v_a_1912_: *mut crate::leanh::LeanObject,
    mut v_a_1913_: *mut crate::leanh::LeanObject,
    mut v_a_1914_: *mut crate::leanh::LeanObject,
    mut v_a_1915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1916_ = l_Lean_Meta_withSharedCtorIndices___redArg(
        v_ctor_1909_,
        v_k_1910_,
        v_a_1911_,
        v_a_1912_,
        v_a_1913_,
        v_a_1914_,
    );
    crate::leanh::lean_dec(v_a_1914_);
    crate::leanh::lean_dec_ref(v_a_1913_);
    crate::leanh::lean_dec(v_a_1912_);
    crate::leanh::lean_dec_ref(v_a_1911_);
    return v_res_1916_;
}
pub unsafe fn l_Lean_Meta_withSharedCtorIndices(
    mut v_00_u03b1_1917_: *mut crate::leanh::LeanObject,
    mut v_ctor_1918_: *mut crate::leanh::LeanObject,
    mut v_k_1919_: *mut crate::leanh::LeanObject,
    mut v_a_1920_: *mut crate::leanh::LeanObject,
    mut v_a_1921_: *mut crate::leanh::LeanObject,
    mut v_a_1922_: *mut crate::leanh::LeanObject,
    mut v_a_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1926_: *mut crate::leanh::LeanObject,
    mut v_ctor_1927_: *mut crate::leanh::LeanObject,
    mut v_k_1928_: *mut crate::leanh::LeanObject,
    mut v_a_1929_: *mut crate::leanh::LeanObject,
    mut v_a_1930_: *mut crate::leanh::LeanObject,
    mut v_a_1931_: *mut crate::leanh::LeanObject,
    mut v_a_1932_: *mut crate::leanh::LeanObject,
    mut v_a_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Lean_Meta_withSharedCtorIndices(
        v_00_u03b1_1926_,
        v_ctor_1927_,
        v_k_1928_,
        v_a_1929_,
        v_a_1930_,
        v_a_1931_,
        v_a_1932_,
    );
    crate::leanh::lean_dec(v_a_1932_);
    crate::leanh::lean_dec_ref(v_a_1931_);
    crate::leanh::lean_dec(v_a_1930_);
    crate::leanh::lean_dec_ref(v_a_1929_);
    return v_res_1934_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_SameCtorUtils(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_SameCtorUtils(
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
pub unsafe fn initialize_Lean_Meta_SameCtorUtils(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_SameCtorUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_SameCtorUtils(builtin);
}
