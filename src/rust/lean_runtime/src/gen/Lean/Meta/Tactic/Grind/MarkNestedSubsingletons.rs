// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Util Lean.Meta.Sym.Util Lean.Meta.Tactic.Grind.Util
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isAppOf,
    l_Lean_Expr_isConstOf, l_Lean_Expr_isForall, l_Lean_Expr_isMData, l_Lean_Expr_isProj,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_instBEqBinderInfo_beq, l_Lean_instInhabitedExpr, l_Lean_mkAppB, l_Lean_mkAppN,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_normalizeLevels,
    l_Lean_Meta_Sym_unfoldReducible, runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, l_Lean_Meta_Grind_eraseIrrelevantMData,
    l_Lean_Meta_Grind_foldProjs, runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
use crate::r#gen::Lean::Meta::Transform::l_Lean_Core_betaReduce;
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_whnfCore;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Profile::l_Lean_profileitIOUnsafe___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [110, 101, 115, 116, 101, 100, 80, 114, 111, 111, 102, 0],
};
static mut l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2_value)
            as *mut crate::leanh::LeanObject,
        1862916703178820790 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        110, 101, 115, 116, 101, 100, 68, 101, 99, 105, 100, 97, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11081308864005098561 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0_value) as *mut crate::leanh::LeanObject,4342836574150310743 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2_value: crate::leanh::LeanStringObject<104> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 104, m_capacity: 104, m_length: 103, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 77, 97, 114, 107, 78, 101, 115, 116, 101, 100, 83, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 115, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 97, 114, 107, 78, 101, 115, 116, 101, 100, 83, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 115, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1_value: crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 77, 97, 114, 107, 78, 101, 115, 116, 101, 100, 83, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_markNestedSubsingletons___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        103, 114, 105, 110, 100, 32, 109, 97, 114, 107, 32, 115, 117, 98, 115, 105, 110, 103, 108,
        101, 116, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Grind_markNestedSubsingletons___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markNestedSubsingletons___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_markNestedSubsingletons___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_markNestedSubsingletons___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_markNestedSubsingletons___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_markNestedSubsingletons___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_isMarkedSubsingletonConst(
    mut v_e_1067_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_1067_) == 4 {
        let mut v_declName_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1070_: u8 = 0;
        v_declName_1068_ = crate::leanh::lean_ctor_get(v_e_1067_, 0);
        v___x_1069_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3;
        v___x_1070_ = lean_name_eq(v_declName_1068_, v___x_1069_);
        if v___x_1070_ == 0 {
            let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1072_: u8 = 0;
            v___x_1071_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5;
            v___x_1072_ = lean_name_eq(v_declName_1068_, v___x_1071_);
            return v___x_1072_;
        } else {
            return v___x_1070_;
        }
    } else {
        let mut v___x_1073_: u8 = 0;
        v___x_1073_ = 0;
        return v___x_1073_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_isMarkedSubsingletonConst___boxed(
    mut v_e_1074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1075_: u8 = 0;
    let mut v_r_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1075_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_e_1074_);
    crate::leanh::lean_dec_ref(v_e_1074_);
    v_r_1076_ = crate::leanh::lean_box((v_res_1075_) as usize);
    return v_r_1076_;
}
pub unsafe fn l_Lean_Meta_Grind_isMarkedSubsingletonApp(
    mut v_e_1077_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    v___x_1078_ = l_Lean_Expr_getAppFn(v_e_1077_);
    v___x_1079_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v___x_1078_);
    crate::leanh::lean_dec_ref(v___x_1078_);
    if v___x_1079_ == 0 {
        return v___x_1079_;
    } else {
        let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1082_: u8 = 0;
        v___x_1080_ = l_Lean_Expr_getAppNumArgs(v_e_1077_);
        v___x_1081_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1082_ = lean_nat_dec_eq(v___x_1080_, v___x_1081_);
        crate::leanh::lean_dec(v___x_1080_);
        return v___x_1082_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_isMarkedSubsingletonApp___boxed(
    mut v_e_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1084_: u8 = 0;
    let mut v_r_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = l_Lean_Meta_Grind_isMarkedSubsingletonApp(v_e_1083_);
    crate::leanh::lean_dec_ref(v_e_1083_);
    v_r_1085_ = crate::leanh::lean_box((v_res_1084_) as usize);
    return v_r_1085_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(
    mut v_e_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
    mut v_a_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1099_: u8 = 0;
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1104_: u8 = 0;
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: u8 = 0;
    let mut v_arg_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1120_: u8 = 0;
    let mut v_a_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1124_: u8 = 0;
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1128_: u8 = 0;
    let mut v_isSharedCheck_1129_: u8 = 0;
    let mut v_a_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1133_: u8 = 0;
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1095_ =
                    l_Lean_Meta_whnfCore(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
                if crate::leanh::lean_obj_tag(v___x_1095_) == 0 {
                    v_a_1096_ = crate::leanh::lean_ctor_get(v___x_1095_, 0);
                    v_isSharedCheck_1129_ = (!crate::leanh::lean_is_exclusive(v___x_1095_)) as u8;
                    if v_isSharedCheck_1129_ == 0 {
                        v___x_1098_ = v___x_1095_;
                        v_isShared_1099_ = v_isSharedCheck_1129_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1096_);
                        crate::leanh::lean_dec(v___x_1095_);
                        v___x_1098_ = crate::leanh::lean_box(0);
                        v_isShared_1099_ = v_isSharedCheck_1129_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1130_ = crate::leanh::lean_ctor_get(v___x_1095_, 0);
                    v_isSharedCheck_1137_ = (!crate::leanh::lean_is_exclusive(v___x_1095_)) as u8;
                    if v_isSharedCheck_1137_ == 0 {
                        v___x_1132_ = v___x_1095_;
                        v_isShared_1133_ = v_isSharedCheck_1137_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1130_);
                        crate::leanh::lean_dec(v___x_1095_);
                        v___x_1132_ = crate::leanh::lean_box(0);
                        v_isShared_1133_ = v_isSharedCheck_1137_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1100_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_1096_, v_a_1091_);
                if crate::leanh::lean_obj_tag(v___x_1100_) == 0 {
                    v_a_1101_ = crate::leanh::lean_ctor_get(v___x_1100_, 0);
                    v_isSharedCheck_1120_ = (!crate::leanh::lean_is_exclusive(v___x_1100_)) as u8;
                    if v_isSharedCheck_1120_ == 0 {
                        v___x_1103_ = v___x_1100_;
                        v_isShared_1104_ = v_isSharedCheck_1120_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1101_);
                        crate::leanh::lean_dec(v___x_1100_);
                        v___x_1103_ = crate::leanh::lean_box(0);
                        v_isShared_1104_ = v_isSharedCheck_1120_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1098_);
                    v_a_1121_ = crate::leanh::lean_ctor_get(v___x_1100_, 0);
                    v_isSharedCheck_1128_ = (!crate::leanh::lean_is_exclusive(v___x_1100_)) as u8;
                    if v_isSharedCheck_1128_ == 0 {
                        v___x_1123_ = v___x_1100_;
                        v_isShared_1124_ = v_isSharedCheck_1128_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1121_);
                        crate::leanh::lean_dec(v___x_1100_);
                        v___x_1123_ = crate::leanh::lean_box(0);
                        v_isShared_1124_ = v_isSharedCheck_1128_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1110_ = l_Lean_Expr_cleanupAnnotations(v_a_1101_);
                v___x_1111_ = l_Lean_Expr_isApp(v___x_1110_);
                if v___x_1111_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1110_);
                    crate::leanh::lean_del_object(v___x_1098_);
                    state = 3;
                    continue;
                } else {
                    v_arg_1112_ = crate::leanh::lean_ctor_get(v___x_1110_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1112_);
                    v___x_1113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1110_);
                    v___x_1114_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1;
                    v___x_1115_ = l_Lean_Expr_isConstOf(v___x_1113_, v___x_1114_);
                    crate::leanh::lean_dec_ref(v___x_1113_);
                    if v___x_1115_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_1112_);
                        crate::leanh::lean_del_object(v___x_1098_);
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_1103_);
                        v___x_1116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1116_, 0, v_arg_1112_);
                        if v_isShared_1099_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1098_, 0, v___x_1116_);
                            v___x_1118_ = v___x_1098_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1119_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
                            v___x_1118_ = v_reuseFailAlloc_1119_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_1106_ = crate::leanh::lean_box(0);
                if v_isShared_1104_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1103_, 0, v___x_1106_);
                    v___x_1108_ = v___x_1103_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
                    v___x_1108_ = v_reuseFailAlloc_1109_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1108_;
            }
            5 => {
                return v___x_1118_;
            }
            6 => {
                if v_isShared_1124_ == 0 {
                    v___x_1126_ = v___x_1123_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
                    v___x_1126_ = v_reuseFailAlloc_1127_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1126_;
            }
            8 => {
                if v_isShared_1133_ == 0 {
                    v___x_1135_ = v___x_1132_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1136_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
                    v___x_1135_ = v_reuseFailAlloc_1136_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___boxed(
    mut v_e_1138_: *mut crate::leanh::LeanObject,
    mut v_a_1139_: *mut crate::leanh::LeanObject,
    mut v_a_1140_: *mut crate::leanh::LeanObject,
    mut v_a_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
    mut v_a_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1144_ =
        l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(
            v_e_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_,
        );
    crate::leanh::lean_dec(v_a_1142_);
    crate::leanh::lean_dec_ref(v_a_1141_);
    crate::leanh::lean_dec(v_a_1140_);
    crate::leanh::lean_dec_ref(v_a_1139_);
    return v_res_1144_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1145_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(
    mut v_msg_1150_: *mut crate::leanh::LeanObject,
    mut v___y_1151_: *mut crate::leanh::LeanObject,
    mut v___y_1152_: *mut crate::leanh::LeanObject,
    mut v___y_1153_: *mut crate::leanh::LeanObject,
    mut v___y_1154_: *mut crate::leanh::LeanObject,
    mut v___y_1155_: *mut crate::leanh::LeanObject,
    mut v___y_1156_: *mut crate::leanh::LeanObject,
    mut v___y_1157_: *mut crate::leanh::LeanObject,
    mut v___y_1158_: *mut crate::leanh::LeanObject,
    mut v___y_1159_: *mut crate::leanh::LeanObject,
    mut v___y_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1167_: u8 = 0;
    let mut v_toFunctor_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v___f_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v_toFunctor_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___f_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71342__overap_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1223_: u8 = 0;
    let mut v_unused_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut v_unused_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1229_: u8 = 0;
    let mut v_unused_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1231_: u8 = 0;
    let mut v_unused_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1162_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0);
                v___x_1163_ = l_StateRefT_x27_instMonad___redArg(v___x_1162_);
                v_toApplicative_1164_ = crate::leanh::lean_ctor_get(v___x_1163_, 0);
                v_isSharedCheck_1231_ = (!crate::leanh::lean_is_exclusive(v___x_1163_)) as u8;
                if v_isSharedCheck_1231_ == 0 {
                    v_unused_1232_ = crate::leanh::lean_ctor_get(v___x_1163_, 1);
                    crate::leanh::lean_dec(v_unused_1232_);
                    v___x_1166_ = v___x_1163_;
                    v_isShared_1167_ = v_isSharedCheck_1231_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1164_);
                    crate::leanh::lean_dec(v___x_1163_);
                    v___x_1166_ = crate::leanh::lean_box(0);
                    v_isShared_1167_ = v_isSharedCheck_1231_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1168_ = crate::leanh::lean_ctor_get(v_toApplicative_1164_, 0);
                v_toSeq_1169_ = crate::leanh::lean_ctor_get(v_toApplicative_1164_, 2);
                v_toSeqLeft_1170_ = crate::leanh::lean_ctor_get(v_toApplicative_1164_, 3);
                v_toSeqRight_1171_ = crate::leanh::lean_ctor_get(v_toApplicative_1164_, 4);
                v_isSharedCheck_1229_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1164_)) as u8;
                if v_isSharedCheck_1229_ == 0 {
                    v_unused_1230_ = crate::leanh::lean_ctor_get(v_toApplicative_1164_, 1);
                    crate::leanh::lean_dec(v_unused_1230_);
                    v___x_1173_ = v_toApplicative_1164_;
                    v_isShared_1174_ = v_isSharedCheck_1229_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1171_);
                    crate::leanh::lean_inc(v_toSeqLeft_1170_);
                    crate::leanh::lean_inc(v_toSeq_1169_);
                    crate::leanh::lean_inc(v_toFunctor_1168_);
                    crate::leanh::lean_dec(v_toApplicative_1164_);
                    v___x_1173_ = crate::leanh::lean_box(0);
                    v_isShared_1174_ = v_isSharedCheck_1229_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1175_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1;
                v___f_1176_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_1168_);
                v___f_1177_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1177_, 0, v_toFunctor_1168_);
                v___f_1178_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1178_, 0, v_toFunctor_1168_);
                v___x_1179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1179_, 0, v___f_1177_);
                crate::leanh::lean_ctor_set(v___x_1179_, 1, v___f_1178_);
                v___f_1180_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1180_, 0, v_toSeqRight_1171_);
                v___f_1181_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1181_, 0, v_toSeqLeft_1170_);
                v___f_1182_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1182_, 0, v_toSeq_1169_);
                if v_isShared_1174_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1173_, 4, v___f_1180_);
                    crate::leanh::lean_ctor_set(v___x_1173_, 3, v___f_1181_);
                    crate::leanh::lean_ctor_set(v___x_1173_, 2, v___f_1182_);
                    crate::leanh::lean_ctor_set(v___x_1173_, 1, v___f_1175_);
                    crate::leanh::lean_ctor_set(v___x_1173_, 0, v___x_1179_);
                    v___x_1184_ = v___x_1173_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1228_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___f_1175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 2, v___f_1182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 3, v___f_1181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 4, v___f_1180_);
                    v___x_1184_ = v_reuseFailAlloc_1228_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1166_, 1, v___f_1176_);
                    crate::leanh::lean_ctor_set(v___x_1166_, 0, v___x_1184_);
                    v___x_1186_ = v___x_1166_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 1, v___f_1176_);
                    v___x_1186_ = v_reuseFailAlloc_1227_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1187_ = l_StateRefT_x27_instMonad___redArg(v___x_1186_);
                v_toApplicative_1188_ = crate::leanh::lean_ctor_get(v___x_1187_, 0);
                v_isSharedCheck_1225_ = (!crate::leanh::lean_is_exclusive(v___x_1187_)) as u8;
                if v_isSharedCheck_1225_ == 0 {
                    v_unused_1226_ = crate::leanh::lean_ctor_get(v___x_1187_, 1);
                    crate::leanh::lean_dec(v_unused_1226_);
                    v___x_1190_ = v___x_1187_;
                    v_isShared_1191_ = v_isSharedCheck_1225_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1188_);
                    crate::leanh::lean_dec(v___x_1187_);
                    v___x_1190_ = crate::leanh::lean_box(0);
                    v_isShared_1191_ = v_isSharedCheck_1225_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1192_ = crate::leanh::lean_ctor_get(v_toApplicative_1188_, 0);
                v_toSeq_1193_ = crate::leanh::lean_ctor_get(v_toApplicative_1188_, 2);
                v_toSeqLeft_1194_ = crate::leanh::lean_ctor_get(v_toApplicative_1188_, 3);
                v_toSeqRight_1195_ = crate::leanh::lean_ctor_get(v_toApplicative_1188_, 4);
                v_isSharedCheck_1223_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1188_)) as u8;
                if v_isSharedCheck_1223_ == 0 {
                    v_unused_1224_ = crate::leanh::lean_ctor_get(v_toApplicative_1188_, 1);
                    crate::leanh::lean_dec(v_unused_1224_);
                    v___x_1197_ = v_toApplicative_1188_;
                    v_isShared_1198_ = v_isSharedCheck_1223_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1195_);
                    crate::leanh::lean_inc(v_toSeqLeft_1194_);
                    crate::leanh::lean_inc(v_toSeq_1193_);
                    crate::leanh::lean_inc(v_toFunctor_1192_);
                    crate::leanh::lean_dec(v_toApplicative_1188_);
                    v___x_1197_ = crate::leanh::lean_box(0);
                    v_isShared_1198_ = v_isSharedCheck_1223_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1199_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3;
                v___f_1200_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_1192_);
                v___f_1201_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1201_, 0, v_toFunctor_1192_);
                v___f_1202_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1202_, 0, v_toFunctor_1192_);
                v___x_1203_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1203_, 0, v___f_1201_);
                crate::leanh::lean_ctor_set(v___x_1203_, 1, v___f_1202_);
                v___f_1204_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1204_, 0, v_toSeqRight_1195_);
                v___f_1205_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1205_, 0, v_toSeqLeft_1194_);
                v___f_1206_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1206_, 0, v_toSeq_1193_);
                if v_isShared_1198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1197_, 4, v___f_1204_);
                    crate::leanh::lean_ctor_set(v___x_1197_, 3, v___f_1205_);
                    crate::leanh::lean_ctor_set(v___x_1197_, 2, v___f_1206_);
                    crate::leanh::lean_ctor_set(v___x_1197_, 1, v___f_1199_);
                    crate::leanh::lean_ctor_set(v___x_1197_, 0, v___x_1203_);
                    v___x_1208_ = v___x_1197_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1222_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___f_1199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 2, v___f_1206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 3, v___f_1205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 4, v___f_1204_);
                    v___x_1208_ = v_reuseFailAlloc_1222_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1191_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1190_, 1, v___f_1200_);
                    crate::leanh::lean_ctor_set(v___x_1190_, 0, v___x_1208_);
                    v___x_1210_ = v___x_1190_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1221_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___f_1200_);
                    v___x_1210_ = v_reuseFailAlloc_1221_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1211_ = l_StateRefT_x27_instMonad___redArg(v___x_1210_);
                v___x_1212_ = l_ReaderT_instMonad___redArg(v___x_1211_);
                v___x_1213_ = l_StateRefT_x27_instMonad___redArg(v___x_1212_);
                v___x_1214_ = l_ReaderT_instMonad___redArg(v___x_1213_);
                v___x_1215_ = l_ReaderT_instMonad___redArg(v___x_1214_);
                v___x_1216_ = l_StateRefT_x27_instMonad___redArg(v___x_1215_);
                v___x_1217_ = l_Lean_instInhabitedExpr;
                v___x_1218_ = l_instInhabitedOfMonad___redArg(v___x_1216_, v___x_1217_);
                v___x_71342__overap_1219_ = lean_panic_fn_borrowed(v___x_1218_, v_msg_1150_);
                crate::leanh::lean_dec(v___x_1218_);
                crate::leanh::lean_inc(v___y_1160_);
                crate::leanh::lean_inc_ref(v___y_1159_);
                crate::leanh::lean_inc(v___y_1158_);
                crate::leanh::lean_inc_ref(v___y_1157_);
                crate::leanh::lean_inc(v___y_1156_);
                crate::leanh::lean_inc_ref(v___y_1155_);
                crate::leanh::lean_inc(v___y_1154_);
                crate::leanh::lean_inc_ref(v___y_1153_);
                crate::leanh::lean_inc(v___y_1152_);
                crate::leanh::lean_inc(v___y_1151_);
                v___x_1220_ = crate::leanh::lean_apply_11(
                    v___x_71342__overap_1219_,
                    v___y_1151_,
                    v___y_1152_,
                    v___y_1153_,
                    v___y_1154_,
                    v___y_1155_,
                    v___y_1156_,
                    v___y_1157_,
                    v___y_1158_,
                    v___y_1159_,
                    v___y_1160_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___boxed(
    mut v_msg_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1245_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(v_msg_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
    crate::leanh::lean_dec(v___y_1243_);
    crate::leanh::lean_dec_ref(v___y_1242_);
    crate::leanh::lean_dec(v___y_1241_);
    crate::leanh::lean_dec_ref(v___y_1240_);
    crate::leanh::lean_dec(v___y_1239_);
    crate::leanh::lean_dec_ref(v___y_1238_);
    crate::leanh::lean_dec(v___y_1237_);
    crate::leanh::lean_dec_ref(v___y_1236_);
    crate::leanh::lean_dec(v___y_1235_);
    crate::leanh::lean_dec(v___y_1234_);
    return v_res_1245_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg(
    mut v_a_1246_: *mut crate::leanh::LeanObject,
    mut v_x_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1247_) == 0 {
                    v___x_1248_ = crate::leanh::lean_box(0);
                    return v___x_1248_;
                } else {
                    v_key_1249_ = crate::leanh::lean_ctor_get(v_x_1247_, 0);
                    v_value_1250_ = crate::leanh::lean_ctor_get(v_x_1247_, 1);
                    v_tail_1251_ = crate::leanh::lean_ctor_get(v_x_1247_, 2);
                    v___x_1252_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_1249_,
                            v_a_1246_,
                        );
                    if v___x_1252_ == 0 {
                        v_x_1247_ = v_tail_1251_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1250_);
                        v___x_1254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1254_, 0, v_value_1250_);
                        return v___x_1254_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg___boxed(
    mut v_a_1255_: *mut crate::leanh::LeanObject,
    mut v_x_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1257_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg(v_a_1255_, v_x_1256_);
    crate::leanh::lean_dec(v_x_1256_);
    crate::leanh::lean_dec_ref(v_a_1255_);
    return v_res_1257_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(
    mut v_m_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: u64 = 0;
    let mut v___x_1263_: u64 = 0;
    let mut v___x_1264_: u64 = 0;
    let mut v_fold_1265_: u64 = 0;
    let mut v___x_1266_: u64 = 0;
    let mut v___x_1267_: u64 = 0;
    let mut v___x_1268_: u64 = 0;
    let mut v___x_1269_: usize = 0;
    let mut v___x_1270_: usize = 0;
    let mut v___x_1271_: usize = 0;
    let mut v___x_1272_: usize = 0;
    let mut v___x_1273_: usize = 0;
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1260_ = crate::leanh::lean_ctor_get(v_m_1258_, 1);
    v___x_1261_ = lean_array_get_size(v_buckets_1260_);
    v___x_1262_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1259_);
    v___x_1263_ = 32u64;
    v___x_1264_ = lean_uint64_shift_right(v___x_1262_, v___x_1263_);
    v_fold_1265_ = lean_uint64_xor(v___x_1262_, v___x_1264_);
    v___x_1266_ = 16u64;
    v___x_1267_ = lean_uint64_shift_right(v_fold_1265_, v___x_1266_);
    v___x_1268_ = lean_uint64_xor(v_fold_1265_, v___x_1267_);
    v___x_1269_ = lean_uint64_to_usize(v___x_1268_);
    v___x_1270_ = lean_usize_of_nat(v___x_1261_);
    v___x_1271_ = 1usize;
    v___x_1272_ = lean_usize_sub(v___x_1270_, v___x_1271_);
    v___x_1273_ = lean_usize_land(v___x_1269_, v___x_1272_);
    v___x_1274_ = lean_array_uget_borrowed(v_buckets_1260_, v___x_1273_);
    v___x_1275_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg(v_a_1259_, v___x_1274_);
    return v___x_1275_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg___boxed(
    mut v_m_1276_: *mut crate::leanh::LeanObject,
    mut v_a_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(v_m_1276_, v_a_1277_);
    crate::leanh::lean_dec_ref(v_a_1277_);
    crate::leanh::lean_dec_ref(v_m_1276_);
    return v_res_1278_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(
    mut v_a_1279_: *mut crate::leanh::LeanObject,
    mut v_b_1280_: *mut crate::leanh::LeanObject,
    mut v_x_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1287_: u8 = 0;
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1281_) == 0 {
                    crate::leanh::lean_dec(v_b_1280_);
                    crate::leanh::lean_dec_ref(v_a_1279_);
                    return v_x_1281_;
                } else {
                    v_key_1282_ = crate::leanh::lean_ctor_get(v_x_1281_, 0);
                    v_value_1283_ = crate::leanh::lean_ctor_get(v_x_1281_, 1);
                    v_tail_1284_ = crate::leanh::lean_ctor_get(v_x_1281_, 2);
                    v_isSharedCheck_1296_ = (!crate::leanh::lean_is_exclusive(v_x_1281_)) as u8;
                    if v_isSharedCheck_1296_ == 0 {
                        v___x_1286_ = v_x_1281_;
                        v_isShared_1287_ = v_isSharedCheck_1296_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1284_);
                        crate::leanh::lean_inc(v_value_1283_);
                        crate::leanh::lean_inc(v_key_1282_);
                        crate::leanh::lean_dec(v_x_1281_);
                        v___x_1286_ = crate::leanh::lean_box(0);
                        v_isShared_1287_ = v_isSharedCheck_1296_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1288_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_key_1282_,
                        v_a_1279_,
                    );
                if v___x_1288_ == 0 {
                    v___x_1289_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(v_a_1279_, v_b_1280_, v_tail_1284_);
                    if v_isShared_1287_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1286_, 2, v___x_1289_);
                        v___x_1291_ = v___x_1286_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1292_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_key_1282_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_value_1283_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 2, v___x_1289_);
                        v___x_1291_ = v_reuseFailAlloc_1292_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1283_);
                    crate::leanh::lean_dec(v_key_1282_);
                    if v_isShared_1287_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1286_, 1, v_b_1280_);
                        crate::leanh::lean_ctor_set(v___x_1286_, 0, v_a_1279_);
                        v___x_1294_ = v___x_1286_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1295_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1279_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_b_1280_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_tail_1284_);
                        v___x_1294_ = v_reuseFailAlloc_1295_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1291_;
            }
            3 => {
                return v___x_1294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9___redArg(
    mut v_x_1297_: *mut crate::leanh::LeanObject,
    mut v_x_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1304_: u8 = 0;
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u64 = 0;
    let mut v___x_1307_: u64 = 0;
    let mut v___x_1308_: u64 = 0;
    let mut v_fold_1309_: u64 = 0;
    let mut v___x_1310_: u64 = 0;
    let mut v___x_1311_: u64 = 0;
    let mut v___x_1312_: u64 = 0;
    let mut v___x_1313_: usize = 0;
    let mut v___x_1314_: usize = 0;
    let mut v___x_1315_: usize = 0;
    let mut v___x_1316_: usize = 0;
    let mut v___x_1317_: usize = 0;
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1298_) == 0 {
                    return v_x_1297_;
                } else {
                    v_key_1299_ = crate::leanh::lean_ctor_get(v_x_1298_, 0);
                    v_value_1300_ = crate::leanh::lean_ctor_get(v_x_1298_, 1);
                    v_tail_1301_ = crate::leanh::lean_ctor_get(v_x_1298_, 2);
                    v_isSharedCheck_1324_ = (!crate::leanh::lean_is_exclusive(v_x_1298_)) as u8;
                    if v_isSharedCheck_1324_ == 0 {
                        v___x_1303_ = v_x_1298_;
                        v_isShared_1304_ = v_isSharedCheck_1324_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1301_);
                        crate::leanh::lean_inc(v_value_1300_);
                        crate::leanh::lean_inc(v_key_1299_);
                        crate::leanh::lean_dec(v_x_1298_);
                        v___x_1303_ = crate::leanh::lean_box(0);
                        v_isShared_1304_ = v_isSharedCheck_1324_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1305_ = lean_array_get_size(v_x_1297_);
                v___x_1306_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_1299_);
                v___x_1307_ = 32u64;
                v___x_1308_ = lean_uint64_shift_right(v___x_1306_, v___x_1307_);
                v_fold_1309_ = lean_uint64_xor(v___x_1306_, v___x_1308_);
                v___x_1310_ = 16u64;
                v___x_1311_ = lean_uint64_shift_right(v_fold_1309_, v___x_1310_);
                v___x_1312_ = lean_uint64_xor(v_fold_1309_, v___x_1311_);
                v___x_1313_ = lean_uint64_to_usize(v___x_1312_);
                v___x_1314_ = lean_usize_of_nat(v___x_1305_);
                v___x_1315_ = 1usize;
                v___x_1316_ = lean_usize_sub(v___x_1314_, v___x_1315_);
                v___x_1317_ = lean_usize_land(v___x_1313_, v___x_1316_);
                v___x_1318_ = lean_array_uget_borrowed(v_x_1297_, v___x_1317_);
                crate::leanh::lean_inc(v___x_1318_);
                if v_isShared_1304_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1303_, 2, v___x_1318_);
                    v___x_1320_ = v___x_1303_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_key_1299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_value_1300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 2, v___x_1318_);
                    v___x_1320_ = v_reuseFailAlloc_1323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1321_ = lean_array_uset(v_x_1297_, v___x_1317_, v___x_1320_);
                v_x_1297_ = v___x_1321_;
                v_x_1298_ = v_tail_1301_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5___redArg(
    mut v_i_1325_: *mut crate::leanh::LeanObject,
    mut v_source_1326_: *mut crate::leanh::LeanObject,
    mut v_target_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: u8 = 0;
    let mut v_es_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1328_ = lean_array_get_size(v_source_1326_);
                v___x_1329_ = lean_nat_dec_lt(v_i_1325_, v___x_1328_);
                if v___x_1329_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1326_);
                    crate::leanh::lean_dec(v_i_1325_);
                    return v_target_1327_;
                } else {
                    v_es_1330_ = lean_array_fget(v_source_1326_, v_i_1325_);
                    v___x_1331_ = crate::leanh::lean_box(0);
                    v_source_1332_ = lean_array_fset(v_source_1326_, v_i_1325_, v___x_1331_);
                    v_target_1333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9___redArg(v_target_1327_, v_es_1330_);
                    v___x_1334_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1335_ = lean_nat_add(v_i_1325_, v___x_1334_);
                    crate::leanh::lean_dec(v_i_1325_);
                    v_i_1325_ = v___x_1335_;
                    v_source_1326_ = v_source_1332_;
                    v_target_1327_ = v_target_1333_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1___redArg(
    mut v_data_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = lean_array_get_size(v_data_1337_);
    v___x_1339_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1340_ = lean_nat_mul(v___x_1338_, v___x_1339_);
    v___x_1341_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1342_ = crate::leanh::lean_box(0);
    v___x_1343_ = lean_mk_array(v_nbuckets_1340_, v___x_1342_);
    v___x_1344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5___redArg(v___x_1341_, v_data_1337_, v___x_1343_);
    return v___x_1344_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg(
    mut v_a_1345_: *mut crate::leanh::LeanObject,
    mut v_x_1346_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1347_: u8 = 0;
    let mut v_key_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1346_) == 0 {
                    v___x_1347_ = 0;
                    return v___x_1347_;
                } else {
                    v_key_1348_ = crate::leanh::lean_ctor_get(v_x_1346_, 0);
                    v_tail_1349_ = crate::leanh::lean_ctor_get(v_x_1346_, 2);
                    v___x_1350_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_1348_,
                            v_a_1345_,
                        );
                    if v___x_1350_ == 0 {
                        v_x_1346_ = v_tail_1349_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1350_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg___boxed(
    mut v_a_1352_: *mut crate::leanh::LeanObject,
    mut v_x_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1354_: u8 = 0;
    let mut v_r_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg(v_a_1352_, v_x_1353_);
    crate::leanh::lean_dec(v_x_1353_);
    crate::leanh::lean_dec_ref(v_a_1352_);
    v_r_1355_ = crate::leanh::lean_box((v_res_1354_) as usize);
    return v_r_1355_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(
    mut v_m_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_b_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: u64 = 0;
    let mut v___x_1366_: u64 = 0;
    let mut v___x_1367_: u64 = 0;
    let mut v_fold_1368_: u64 = 0;
    let mut v___x_1369_: u64 = 0;
    let mut v___x_1370_: u64 = 0;
    let mut v___x_1371_: u64 = 0;
    let mut v___x_1372_: usize = 0;
    let mut v___x_1373_: usize = 0;
    let mut v___x_1374_: usize = 0;
    let mut v___x_1375_: usize = 0;
    let mut v___x_1376_: usize = 0;
    let mut v_bkt_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v_val_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1359_ = crate::leanh::lean_ctor_get(v_m_1356_, 0);
                v_buckets_1360_ = crate::leanh::lean_ctor_get(v_m_1356_, 1);
                v_isSharedCheck_1403_ = (!crate::leanh::lean_is_exclusive(v_m_1356_)) as u8;
                if v_isSharedCheck_1403_ == 0 {
                    v___x_1362_ = v_m_1356_;
                    v_isShared_1363_ = v_isSharedCheck_1403_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1360_);
                    crate::leanh::lean_inc(v_size_1359_);
                    crate::leanh::lean_dec(v_m_1356_);
                    v___x_1362_ = crate::leanh::lean_box(0);
                    v_isShared_1363_ = v_isSharedCheck_1403_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1364_ = lean_array_get_size(v_buckets_1360_);
                v___x_1365_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1357_);
                v___x_1366_ = 32u64;
                v___x_1367_ = lean_uint64_shift_right(v___x_1365_, v___x_1366_);
                v_fold_1368_ = lean_uint64_xor(v___x_1365_, v___x_1367_);
                v___x_1369_ = 16u64;
                v___x_1370_ = lean_uint64_shift_right(v_fold_1368_, v___x_1369_);
                v___x_1371_ = lean_uint64_xor(v_fold_1368_, v___x_1370_);
                v___x_1372_ = lean_uint64_to_usize(v___x_1371_);
                v___x_1373_ = lean_usize_of_nat(v___x_1364_);
                v___x_1374_ = 1usize;
                v___x_1375_ = lean_usize_sub(v___x_1373_, v___x_1374_);
                v___x_1376_ = lean_usize_land(v___x_1372_, v___x_1375_);
                v_bkt_1377_ = lean_array_uget_borrowed(v_buckets_1360_, v___x_1376_);
                v___x_1378_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg(v_a_1357_, v_bkt_1377_);
                if v___x_1378_ == 0 {
                    v___x_1379_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1380_ = lean_nat_add(v_size_1359_, v___x_1379_);
                    crate::leanh::lean_dec(v_size_1359_);
                    crate::leanh::lean_inc(v_bkt_1377_);
                    v___x_1381_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1381_, 0, v_a_1357_);
                    crate::leanh::lean_ctor_set(v___x_1381_, 1, v_b_1358_);
                    crate::leanh::lean_ctor_set(v___x_1381_, 2, v_bkt_1377_);
                    v_buckets_x27_1382_ =
                        lean_array_uset(v_buckets_1360_, v___x_1376_, v___x_1381_);
                    v___x_1383_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1384_ = lean_nat_mul(v_size_x27_1380_, v___x_1383_);
                    v___x_1385_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1386_ = lean_nat_div(v___x_1384_, v___x_1385_);
                    crate::leanh::lean_dec(v___x_1384_);
                    v___x_1387_ = lean_array_get_size(v_buckets_x27_1382_);
                    v___x_1388_ = lean_nat_dec_le(v___x_1386_, v___x_1387_);
                    crate::leanh::lean_dec(v___x_1386_);
                    if v___x_1388_ == 0 {
                        v_val_1389_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1___redArg(v_buckets_x27_1382_);
                        if v_isShared_1363_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1362_, 1, v_val_1389_);
                            crate::leanh::lean_ctor_set(v___x_1362_, 0, v_size_x27_1380_);
                            v___x_1391_ = v___x_1362_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1392_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1392_,
                                0,
                                v_size_x27_1380_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_val_1389_);
                            v___x_1391_ = v_reuseFailAlloc_1392_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1363_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1362_, 1, v_buckets_x27_1382_);
                            crate::leanh::lean_ctor_set(v___x_1362_, 0, v_size_x27_1380_);
                            v___x_1394_ = v___x_1362_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1395_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1395_,
                                0,
                                v_size_x27_1380_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1395_,
                                1,
                                v_buckets_x27_1382_,
                            );
                            v___x_1394_ = v_reuseFailAlloc_1395_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1377_);
                    v___x_1396_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1397_ =
                        lean_array_uset(v_buckets_1360_, v___x_1376_, v___x_1396_);
                    v___x_1398_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(v_a_1357_, v_b_1358_, v_bkt_1377_);
                    v___x_1399_ = lean_array_uset(v_buckets_x27_1397_, v___x_1376_, v___x_1398_);
                    if v_isShared_1363_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1362_, 1, v___x_1399_);
                        v___x_1401_ = v___x_1362_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_size_1359_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___x_1399_);
                        v___x_1401_ = v_reuseFailAlloc_1402_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1391_;
            }
            3 => {
                return v___x_1394_;
            }
            4 => {
                return v___x_1401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg(
    mut v_e_1404_: *mut crate::leanh::LeanObject,
    mut v___y_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: u8 = 0;
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1421_: u8 = 0;
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1427_: u8 = 0;
    let mut v_unused_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1407_ = l_Lean_Expr_hasMVar(v_e_1404_);
                if v___x_1407_ == 0 {
                    v___x_1408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1408_, 0, v_e_1404_);
                    return v___x_1408_;
                } else {
                    v___x_1409_ = lean_st_ref_get(v___y_1405_);
                    v_mctx_1410_ = crate::leanh::lean_ctor_get(v___x_1409_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1410_);
                    crate::leanh::lean_dec(v___x_1409_);
                    v___x_1411_ = l_Lean_instantiateMVarsCore(v_mctx_1410_, v_e_1404_);
                    v_fst_1412_ = crate::leanh::lean_ctor_get(v___x_1411_, 0);
                    crate::leanh::lean_inc(v_fst_1412_);
                    v_snd_1413_ = crate::leanh::lean_ctor_get(v___x_1411_, 1);
                    crate::leanh::lean_inc(v_snd_1413_);
                    crate::leanh::lean_dec_ref(v___x_1411_);
                    v___x_1414_ = lean_st_ref_take(v___y_1405_);
                    v_cache_1415_ = crate::leanh::lean_ctor_get(v___x_1414_, 1);
                    v_zetaDeltaFVarIds_1416_ = crate::leanh::lean_ctor_get(v___x_1414_, 2);
                    v_postponed_1417_ = crate::leanh::lean_ctor_get(v___x_1414_, 3);
                    v_diag_1418_ = crate::leanh::lean_ctor_get(v___x_1414_, 4);
                    v_isSharedCheck_1427_ = (!crate::leanh::lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1427_ == 0 {
                        v_unused_1428_ = crate::leanh::lean_ctor_get(v___x_1414_, 0);
                        crate::leanh::lean_dec(v_unused_1428_);
                        v___x_1420_ = v___x_1414_;
                        v_isShared_1421_ = v_isSharedCheck_1427_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1418_);
                        crate::leanh::lean_inc(v_postponed_1417_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1416_);
                        crate::leanh::lean_inc(v_cache_1415_);
                        crate::leanh::lean_dec(v___x_1414_);
                        v___x_1420_ = crate::leanh::lean_box(0);
                        v_isShared_1421_ = v_isSharedCheck_1427_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1421_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1420_, 0, v_snd_1413_);
                    v___x_1423_ = v___x_1420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1426_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_snd_1413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_cache_1415_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1426_,
                        2,
                        v_zetaDeltaFVarIds_1416_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_postponed_1417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 4, v_diag_1418_);
                    v___x_1423_ = v_reuseFailAlloc_1426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1424_ = lean_st_ref_set(v___y_1405_, v___x_1423_);
                v___x_1425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1425_, 0, v_fst_1412_);
                return v___x_1425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg___boxed(
    mut v_e_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1432_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg(v_e_1429_, v___y_1430_);
    crate::leanh::lean_dec(v___y_1430_);
    return v_res_1432_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = crate::leanh::lean_box(0);
    v_dummy_1434_ = l_Lean_Expr_sort___override(v___x_1433_);
    return v_dummy_1434_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3;
    v___x_1439_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_1440_ = crate::leanh::lean_unsigned_to_nat(89);
    v___x_1441_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2;
    v___x_1442_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1;
    v___x_1443_ = l_mkPanicMessageWithDecl(
        v___x_1442_,
        v___x_1441_,
        v___x_1440_,
        v___x_1439_,
        v___x_1438_,
    );
    return v___x_1443_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(
    mut v_e_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
    mut v_a_1446_: *mut crate::leanh::LeanObject,
    mut v_a_1447_: *mut crate::leanh::LeanObject,
    mut v_a_1448_: *mut crate::leanh::LeanObject,
    mut v_a_1449_: *mut crate::leanh::LeanObject,
    mut v_a_1450_: *mut crate::leanh::LeanObject,
    mut v_a_1451_: *mut crate::leanh::LeanObject,
    mut v_a_1452_: *mut crate::leanh::LeanObject,
    mut v_a_1453_: *mut crate::leanh::LeanObject,
    mut v_a_1454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1456_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg(v_e_1444_, v_a_1452_);
    if crate::leanh::lean_obj_tag(v___x_1456_) == 0 {
        let mut v_a_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1457_ = crate::leanh::lean_ctor_get(v___x_1456_, 0);
        crate::leanh::lean_inc(v_a_1457_);
        crate::leanh::lean_dec_ref_known(v___x_1456_, 1);
        v___x_1458_ = l_Lean_Core_betaReduce(v_a_1457_, v_a_1453_, v_a_1454_);
        if crate::leanh::lean_obj_tag(v___x_1458_) == 0 {
            let mut v_a_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1459_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
            crate::leanh::lean_inc(v_a_1459_);
            crate::leanh::lean_dec_ref_known(v___x_1458_, 1);
            v___x_1460_ = l_Lean_Meta_Sym_unfoldReducible(
                v_a_1459_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_,
            );
            if crate::leanh::lean_obj_tag(v___x_1460_) == 0 {
                let mut v_a_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_1461_ = crate::leanh::lean_ctor_get(v___x_1460_, 0);
                crate::leanh::lean_inc(v_a_1461_);
                crate::leanh::lean_dec_ref_known(v___x_1460_, 1);
                v___x_1462_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_a_1461_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
                if crate::leanh::lean_obj_tag(v___x_1462_) == 0 {
                    let mut v_a_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_a_1463_ = crate::leanh::lean_ctor_get(v___x_1462_, 0);
                    crate::leanh::lean_inc(v_a_1463_);
                    crate::leanh::lean_dec_ref_known(v___x_1462_, 1);
                    v___x_1464_ =
                        l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_1463_, v_a_1453_, v_a_1454_);
                    if crate::leanh::lean_obj_tag(v___x_1464_) == 0 {
                        let mut v_a_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_a_1465_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                        crate::leanh::lean_inc(v_a_1465_);
                        crate::leanh::lean_dec_ref_known(v___x_1464_, 1);
                        v___x_1466_ = l_Lean_Meta_Grind_foldProjs(
                            v_a_1465_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1466_) == 0 {
                            let mut v_a_1467_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1468_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v_a_1467_ = crate::leanh::lean_ctor_get(v___x_1466_, 0);
                            crate::leanh::lean_inc(v_a_1467_);
                            crate::leanh::lean_dec_ref_known(v___x_1466_, 1);
                            v___x_1468_ =
                                l_Lean_Meta_Sym_normalizeLevels(v_a_1467_, v_a_1453_, v_a_1454_);
                            return v___x_1468_;
                        } else {
                            return v___x_1466_;
                        }
                    } else {
                        return v___x_1464_;
                    }
                } else {
                    return v___x_1462_;
                }
            } else {
                return v___x_1460_;
            }
        } else {
            return v___x_1458_;
        }
    } else {
        return v___x_1456_;
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1469_ = crate::leanh::lean_box(0);
    v___x_1470_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5;
    v___x_1471_ = l_Lean_mkConst(v___x_1470_, v___x_1469_);
    return v___x_1471_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1472_ = crate::leanh::lean_box(0);
    v___x_1473_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3;
    v___x_1474_ = l_Lean_mkConst(v___x_1473_, v___x_1472_);
    return v___x_1474_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(
    mut v_e_1475_: *mut crate::leanh::LeanObject,
    mut v_a_1476_: *mut crate::leanh::LeanObject,
    mut v_a_1477_: *mut crate::leanh::LeanObject,
    mut v_a_1478_: *mut crate::leanh::LeanObject,
    mut v_a_1479_: *mut crate::leanh::LeanObject,
    mut v_a_1480_: *mut crate::leanh::LeanObject,
    mut v_a_1481_: *mut crate::leanh::LeanObject,
    mut v_a_1482_: *mut crate::leanh::LeanObject,
    mut v_a_1483_: *mut crate::leanh::LeanObject,
    mut v_a_1484_: *mut crate::leanh::LeanObject,
    mut v_a_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_x27_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1497_: u8 = 0;
    let mut v___y_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1508_: u8 = 0;
    let mut v___y_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_x27_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: usize = 0;
    let mut v___x_1513_: usize = 0;
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: usize = 0;
    let mut v___x_1516_: usize = 0;
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v_dummy_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: usize = 0;
    let mut v___x_1554_: usize = 0;
    let mut v___x_1555_: u8 = 0;
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: usize = 0;
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1568_: u8 = 0;
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v___x_1592_: u8 = 0;
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: u8 = 0;
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_a_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_a_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1518_ = l_Lean_Meta_Grind_isMarkedSubsingletonApp(v_e_1475_);
                if v___x_1518_ == 0 {
                    v___x_1519_ = lean_st_ref_get(v_a_1476_);
                    v___x_1520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(v___x_1519_, v_e_1475_);
                    crate::leanh::lean_dec(v___x_1519_);
                    if crate::leanh::lean_obj_tag(v___x_1520_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_1475_);
                        v_val_1521_ = crate::leanh::lean_ctor_get(v___x_1520_, 0);
                        v_isSharedCheck_1528_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1520_)) as u8;
                        if v_isSharedCheck_1528_ == 0 {
                            v___x_1523_ = v___x_1520_;
                            v_isShared_1524_ = v_isSharedCheck_1528_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1521_);
                            crate::leanh::lean_dec(v___x_1520_);
                            v___x_1523_ = crate::leanh::lean_box(0);
                            v_isShared_1524_ = v_isSharedCheck_1528_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1520_);
                        crate::leanh::lean_inc(v_a_1485_);
                        crate::leanh::lean_inc_ref(v_a_1484_);
                        crate::leanh::lean_inc(v_a_1483_);
                        crate::leanh::lean_inc_ref(v_a_1482_);
                        crate::leanh::lean_inc_ref(v_e_1475_);
                        v___x_1529_ =
                            lean_infer_type(v_e_1475_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                        if crate::leanh::lean_obj_tag(v___x_1529_) == 0 {
                            v_a_1530_ = crate::leanh::lean_ctor_get(v___x_1529_, 0);
                            crate::leanh::lean_inc_n(v_a_1530_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_1529_, 1);
                            v___x_1531_ = l_Lean_Meta_isProp(
                                v_a_1530_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1531_) == 0 {
                                v_a_1532_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                                crate::leanh::lean_inc(v_a_1532_);
                                crate::leanh::lean_dec_ref_known(v___x_1531_, 1);
                                v___x_1533_ = (crate::leanh::lean_unbox(v_a_1532_) as u8);
                                if v___x_1533_ == 0 {
                                    v___x_1534_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(v_a_1530_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                                    if crate::leanh::lean_obj_tag(v___x_1534_) == 0 {
                                        v_a_1535_ = crate::leanh::lean_ctor_get(v___x_1534_, 0);
                                        v_isSharedCheck_1599_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1534_)) as u8;
                                        if v_isSharedCheck_1599_ == 0 {
                                            v___x_1537_ = v___x_1534_;
                                            v_isShared_1538_ = v_isSharedCheck_1599_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1535_);
                                            crate::leanh::lean_dec(v___x_1534_);
                                            v___x_1537_ = crate::leanh::lean_box(0);
                                            v_isShared_1538_ = v_isSharedCheck_1599_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1532_);
                                        crate::leanh::lean_dec_ref(v_e_1475_);
                                        v_a_1600_ = crate::leanh::lean_ctor_get(v___x_1534_, 0);
                                        v_isSharedCheck_1607_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1534_)) as u8;
                                        if v_isSharedCheck_1607_ == 0 {
                                            v___x_1602_ = v___x_1534_;
                                            v_isShared_1603_ = v_isSharedCheck_1607_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1600_);
                                            crate::leanh::lean_dec(v___x_1534_);
                                            v___x_1602_ = crate::leanh::lean_box(0);
                                            v_isShared_1603_ = v_isSharedCheck_1607_;
                                            state = 11;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1532_);
                                    v___x_1608_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_a_1530_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                                    if crate::leanh::lean_obj_tag(v___x_1608_) == 0 {
                                        v_a_1609_ = crate::leanh::lean_ctor_get(v___x_1608_, 0);
                                        v_isSharedCheck_1621_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1608_)) as u8;
                                        if v_isSharedCheck_1621_ == 0 {
                                            v___x_1611_ = v___x_1608_;
                                            v_isShared_1612_ = v_isSharedCheck_1621_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1609_);
                                            crate::leanh::lean_dec(v___x_1608_);
                                            v___x_1611_ = crate::leanh::lean_box(0);
                                            v_isShared_1612_ = v_isSharedCheck_1621_;
                                            state = 13;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_e_1475_);
                                        return v___x_1608_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1530_);
                                crate::leanh::lean_dec_ref(v_e_1475_);
                                v_a_1622_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                                v_isSharedCheck_1629_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1531_)) as u8;
                                if v_isSharedCheck_1629_ == 0 {
                                    v___x_1624_ = v___x_1531_;
                                    v_isShared_1625_ = v_isSharedCheck_1629_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1622_);
                                    crate::leanh::lean_dec(v___x_1531_);
                                    v___x_1624_ = crate::leanh::lean_box(0);
                                    v_isShared_1625_ = v_isSharedCheck_1629_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_1475_);
                            return v___x_1529_;
                        }
                    }
                } else {
                    v___x_1630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1630_, 0, v_e_1475_);
                    return v___x_1630_;
                }
            }
            1 => {
                v___x_1490_ = lean_st_ref_take(v___y_1489_);
                crate::leanh::lean_inc_ref(v_e_x27_1488_);
                v___x_1491_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v___x_1490_, v_e_1475_, v_e_x27_1488_);
                v___x_1492_ = lean_st_ref_set(v___y_1489_, v___x_1491_);
                v___x_1493_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1493_, 0, v_e_x27_1488_);
                return v___x_1493_;
            }
            2 => {
                if v___y_1500_ == 0 {
                    v___x_1501_ = l_Lean_Expr_forallE___override(
                        v___y_1499_,
                        v___y_1495_,
                        v___y_1498_,
                        v___y_1497_,
                    );
                    v_e_x27_1488_ = v___x_1501_;
                    v___y_1489_ = v___y_1496_;
                    state = 1;
                    continue;
                } else {
                    v___x_1502_ = l_Lean_instBEqBinderInfo_beq(v___y_1497_, v___y_1497_);
                    if v___x_1502_ == 0 {
                        v___x_1503_ = l_Lean_Expr_forallE___override(
                            v___y_1499_,
                            v___y_1495_,
                            v___y_1498_,
                            v___y_1497_,
                        );
                        v_e_x27_1488_ = v___x_1503_;
                        v___y_1489_ = v___y_1496_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_1499_);
                        crate::leanh::lean_dec_ref(v___y_1498_);
                        crate::leanh::lean_dec_ref(v___y_1495_);
                        crate::leanh::lean_inc_ref(v_e_1475_);
                        v_e_x27_1488_ = v_e_1475_;
                        v___y_1489_ = v___y_1496_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1512_ = lean_ptr_addr(v___y_1506_);
                crate::leanh::lean_dec_ref(v___y_1506_);
                v___x_1513_ = lean_ptr_addr(v___y_1505_);
                v___x_1514_ = lean_usize_dec_eq(v___x_1512_, v___x_1513_);
                if v___x_1514_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1507_);
                    v___y_1495_ = v___y_1505_;
                    v___y_1496_ = v___y_1511_;
                    v___y_1497_ = v___y_1508_;
                    v___y_1498_ = v_b_x27_1510_;
                    v___y_1499_ = v___y_1509_;
                    v___y_1500_ = v___x_1514_;
                    state = 2;
                    continue;
                } else {
                    v___x_1515_ = lean_ptr_addr(v___y_1507_);
                    crate::leanh::lean_dec_ref(v___y_1507_);
                    v___x_1516_ = lean_ptr_addr(v_b_x27_1510_);
                    v___x_1517_ = lean_usize_dec_eq(v___x_1515_, v___x_1516_);
                    v___y_1495_ = v___y_1505_;
                    v___y_1496_ = v___y_1511_;
                    v___y_1497_ = v___y_1508_;
                    v___y_1498_ = v_b_x27_1510_;
                    v___y_1499_ = v___y_1509_;
                    v___y_1500_ = v___x_1517_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_1524_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1523_, 0);
                    v___x_1526_ = v___x_1523_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_val_1521_);
                    v___x_1526_ = v_reuseFailAlloc_1527_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1526_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_1535_) == 1 {
                    crate::leanh::lean_del_object(v___x_1537_);
                    crate::leanh::lean_dec(v_a_1532_);
                    v_val_1577_ = crate::leanh::lean_ctor_get(v_a_1535_, 0);
                    crate::leanh::lean_inc(v_val_1577_);
                    crate::leanh::lean_dec_ref_known(v_a_1535_, 1);
                    v___x_1578_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_val_1577_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                    if crate::leanh::lean_obj_tag(v___x_1578_) == 0 {
                        v_a_1579_ = crate::leanh::lean_ctor_get(v___x_1578_, 0);
                        v_isSharedCheck_1591_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1578_)) as u8;
                        if v_isSharedCheck_1591_ == 0 {
                            v___x_1581_ = v___x_1578_;
                            v_isShared_1582_ = v_isSharedCheck_1591_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1579_);
                            crate::leanh::lean_dec(v___x_1578_);
                            v___x_1581_ = crate::leanh::lean_box(0);
                            v_isShared_1582_ = v_isSharedCheck_1591_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1475_);
                        return v___x_1578_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1535_);
                    v___x_1592_ = l_Lean_Expr_isApp(v_e_1475_);
                    if v___x_1592_ == 0 {
                        v___x_1593_ = l_Lean_Expr_isForall(v_e_1475_);
                        if v___x_1593_ == 0 {
                            v___x_1594_ = l_Lean_Expr_isProj(v_e_1475_);
                            if v___x_1594_ == 0 {
                                v___x_1595_ = l_Lean_Expr_isMData(v_e_1475_);
                                if v___x_1595_ == 0 {
                                    crate::leanh::lean_dec(v_a_1532_);
                                    if v_isShared_1538_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1537_, 0, v_e_1475_);
                                        v___x_1597_ = v___x_1537_;
                                        state = 10;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1598_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1598_,
                                            0,
                                            v_e_1475_,
                                        );
                                        v___x_1597_ = v_reuseFailAlloc_1598_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_1537_);
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_1537_);
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1537_);
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1537_);
                        state = 7;
                        continue;
                    }
                }
            }
            7 => match crate::leanh::lean_obj_tag(v_e_1475_) {
                5 => {
                    v_dummy_1540_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0);
                    v_nargs_1541_ = l_Lean_Expr_getAppNumArgs(v_e_1475_);
                    crate::leanh::lean_inc(v_nargs_1541_);
                    v___x_1542_ = lean_mk_array(v_nargs_1541_, v_dummy_1540_);
                    v___x_1543_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1544_ = lean_nat_sub(v_nargs_1541_, v___x_1543_);
                    crate::leanh::lean_dec(v_nargs_1541_);
                    v___x_1545_ = (crate::leanh::lean_unbox(v_a_1532_) as u8);
                    crate::leanh::lean_dec(v_a_1532_);
                    crate::leanh::lean_inc_ref_n(v_e_1475_, 2);
                    v___x_1546_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(v_e_1475_, v___x_1545_, v_e_1475_, v___x_1542_, v___x_1544_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                    if crate::leanh::lean_obj_tag(v___x_1546_) == 0 {
                        v_a_1547_ = crate::leanh::lean_ctor_get(v___x_1546_, 0);
                        crate::leanh::lean_inc(v_a_1547_);
                        crate::leanh::lean_dec_ref_known(v___x_1546_, 1);
                        v_e_x27_1488_ = v_a_1547_;
                        v___y_1489_ = v_a_1476_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_1475_, 2);
                        return v___x_1546_;
                    }
                }
                11 => {
                    crate::leanh::lean_dec(v_a_1532_);
                    v_typeName_1548_ = crate::leanh::lean_ctor_get(v_e_1475_, 0);
                    v_idx_1549_ = crate::leanh::lean_ctor_get(v_e_1475_, 1);
                    v_struct_1550_ = crate::leanh::lean_ctor_get(v_e_1475_, 2);
                    crate::leanh::lean_inc_ref(v_struct_1550_);
                    v___x_1551_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_struct_1550_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                    if crate::leanh::lean_obj_tag(v___x_1551_) == 0 {
                        v_a_1552_ = crate::leanh::lean_ctor_get(v___x_1551_, 0);
                        crate::leanh::lean_inc(v_a_1552_);
                        crate::leanh::lean_dec_ref_known(v___x_1551_, 1);
                        v___x_1553_ = lean_ptr_addr(v_struct_1550_);
                        v___x_1554_ = lean_ptr_addr(v_a_1552_);
                        v___x_1555_ = lean_usize_dec_eq(v___x_1553_, v___x_1554_);
                        if v___x_1555_ == 0 {
                            crate::leanh::lean_inc(v_idx_1549_);
                            crate::leanh::lean_inc(v_typeName_1548_);
                            v___x_1556_ = l_Lean_Expr_proj___override(
                                v_typeName_1548_,
                                v_idx_1549_,
                                v_a_1552_,
                            );
                            v_e_x27_1488_ = v___x_1556_;
                            v___y_1489_ = v_a_1476_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1552_);
                            crate::leanh::lean_inc_ref(v_e_1475_);
                            v_e_x27_1488_ = v_e_1475_;
                            v___y_1489_ = v_a_1476_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_1475_, 3);
                        return v___x_1551_;
                    }
                }
                10 => {
                    crate::leanh::lean_dec(v_a_1532_);
                    v_data_1557_ = crate::leanh::lean_ctor_get(v_e_1475_, 0);
                    v_expr_1558_ = crate::leanh::lean_ctor_get(v_e_1475_, 1);
                    crate::leanh::lean_inc_ref(v_expr_1558_);
                    v___x_1559_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_expr_1558_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                    if crate::leanh::lean_obj_tag(v___x_1559_) == 0 {
                        v_a_1560_ = crate::leanh::lean_ctor_get(v___x_1559_, 0);
                        crate::leanh::lean_inc(v_a_1560_);
                        crate::leanh::lean_dec_ref_known(v___x_1559_, 1);
                        v___x_1561_ = lean_ptr_addr(v_expr_1558_);
                        v___x_1562_ = lean_ptr_addr(v_a_1560_);
                        v___x_1563_ = lean_usize_dec_eq(v___x_1561_, v___x_1562_);
                        if v___x_1563_ == 0 {
                            crate::leanh::lean_inc(v_data_1557_);
                            v___x_1564_ = l_Lean_Expr_mdata___override(v_data_1557_, v_a_1560_);
                            v_e_x27_1488_ = v___x_1564_;
                            v___y_1489_ = v_a_1476_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1560_);
                            crate::leanh::lean_inc_ref(v_e_1475_);
                            v_e_x27_1488_ = v_e_1475_;
                            v___y_1489_ = v_a_1476_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_1475_, 2);
                        return v___x_1559_;
                    }
                }
                7 => {
                    crate::leanh::lean_dec(v_a_1532_);
                    v_binderName_1565_ = crate::leanh::lean_ctor_get(v_e_1475_, 0);
                    v_binderType_1566_ = crate::leanh::lean_ctor_get(v_e_1475_, 1);
                    v_body_1567_ = crate::leanh::lean_ctor_get(v_e_1475_, 2);
                    v_binderInfo_1568_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_1475_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_1566_);
                    v___x_1569_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_binderType_1566_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                    if crate::leanh::lean_obj_tag(v___x_1569_) == 0 {
                        v_a_1570_ = crate::leanh::lean_ctor_get(v___x_1569_, 0);
                        crate::leanh::lean_inc(v_a_1570_);
                        crate::leanh::lean_dec_ref_known(v___x_1569_, 1);
                        v___x_1571_ = l_Lean_Expr_hasLooseBVars(v_body_1567_);
                        if v___x_1571_ == 0 {
                            crate::leanh::lean_inc_ref(v_body_1567_);
                            v___x_1572_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_body_1567_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                            if crate::leanh::lean_obj_tag(v___x_1572_) == 0 {
                                v_a_1573_ = crate::leanh::lean_ctor_get(v___x_1572_, 0);
                                crate::leanh::lean_inc(v_a_1573_);
                                crate::leanh::lean_dec_ref_known(v___x_1572_, 1);
                                crate::leanh::lean_inc(v_binderName_1565_);
                                crate::leanh::lean_inc_ref(v_body_1567_);
                                crate::leanh::lean_inc_ref(v_binderType_1566_);
                                v___y_1505_ = v_a_1570_;
                                v___y_1506_ = v_binderType_1566_;
                                v___y_1507_ = v_body_1567_;
                                v___y_1508_ = v_binderInfo_1568_;
                                v___y_1509_ = v_binderName_1565_;
                                v_b_x27_1510_ = v_a_1573_;
                                v___y_1511_ = v_a_1476_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1570_);
                                crate::leanh::lean_dec_ref_known(v_e_1475_, 3);
                                return v___x_1572_;
                            }
                        } else {
                            crate::leanh::lean_inc(v_binderName_1565_);
                            crate::leanh::lean_inc_ref_n(v_body_1567_, 2);
                            crate::leanh::lean_inc_ref(v_binderType_1566_);
                            v___y_1505_ = v_a_1570_;
                            v___y_1506_ = v_binderType_1566_;
                            v___y_1507_ = v_body_1567_;
                            v___y_1508_ = v_binderInfo_1568_;
                            v___y_1509_ = v_binderName_1565_;
                            v_b_x27_1510_ = v_body_1567_;
                            v___y_1511_ = v_a_1476_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_1475_, 3);
                        return v___x_1569_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_a_1532_);
                    v___x_1574_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4);
                    v___x_1575_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(v___x_1574_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
                    if crate::leanh::lean_obj_tag(v___x_1575_) == 0 {
                        v_a_1576_ = crate::leanh::lean_ctor_get(v___x_1575_, 0);
                        crate::leanh::lean_inc(v_a_1576_);
                        crate::leanh::lean_dec_ref_known(v___x_1575_, 1);
                        v_e_x27_1488_ = v_a_1576_;
                        v___y_1489_ = v_a_1476_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1475_);
                        return v___x_1575_;
                    }
                }
            },
            8 => {
                v___x_1583_ = lean_st_ref_take(v_a_1476_);
                v___x_1584_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5);
                crate::leanh::lean_inc_ref(v_e_1475_);
                v___x_1585_ = l_Lean_mkAppB(v___x_1584_, v_a_1579_, v_e_1475_);
                crate::leanh::lean_inc_ref(v___x_1585_);
                v___x_1586_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v___x_1583_, v_e_1475_, v___x_1585_);
                v___x_1587_ = lean_st_ref_set(v_a_1476_, v___x_1586_);
                if v_isShared_1582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1581_, 0, v___x_1585_);
                    v___x_1589_ = v___x_1581_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1590_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1585_);
                    v___x_1589_ = v_reuseFailAlloc_1590_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1589_;
            }
            10 => {
                return v___x_1597_;
            }
            11 => {
                if v_isShared_1603_ == 0 {
                    v___x_1605_ = v___x_1602_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
                    v___x_1605_ = v_reuseFailAlloc_1606_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1605_;
            }
            13 => {
                v___x_1613_ = lean_st_ref_take(v_a_1476_);
                v___x_1614_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6);
                crate::leanh::lean_inc_ref(v_e_1475_);
                v___x_1615_ = l_Lean_mkAppB(v___x_1614_, v_a_1609_, v_e_1475_);
                crate::leanh::lean_inc_ref(v___x_1615_);
                v___x_1616_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v___x_1613_, v_e_1475_, v___x_1615_);
                v___x_1617_ = lean_st_ref_set(v_a_1476_, v___x_1616_);
                if v_isShared_1612_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1611_, 0, v___x_1615_);
                    v___x_1619_ = v___x_1611_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1620_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1615_);
                    v___x_1619_ = v_reuseFailAlloc_1620_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1619_;
            }
            15 => {
                if v_isShared_1625_ == 0 {
                    v___x_1627_ = v___x_1624_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1628_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
                    v___x_1627_ = v_reuseFailAlloc_1628_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(
    mut v_upperBound_1631_: *mut crate::leanh::LeanObject,
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v_b_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
    mut v___y_1635_: *mut crate::leanh::LeanObject,
    mut v___y_1636_: *mut crate::leanh::LeanObject,
    mut v___y_1637_: *mut crate::leanh::LeanObject,
    mut v___y_1638_: *mut crate::leanh::LeanObject,
    mut v___y_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modified_1645_: u8 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1676_: u8 = 0;
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_modified_1645_ = lean_nat_dec_lt(v_a_1632_, v_upperBound_1631_);
                if v_modified_1645_ == 0 {
                    crate::leanh::lean_dec(v_a_1632_);
                    v___x_1646_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1646_, 0, v_b_1633_);
                    return v___x_1646_;
                } else {
                    v_fst_1647_ = crate::leanh::lean_ctor_get(v_b_1633_, 0);
                    v_snd_1648_ = crate::leanh::lean_ctor_get(v_b_1633_, 1);
                    v_isSharedCheck_1677_ = (!crate::leanh::lean_is_exclusive(v_b_1633_)) as u8;
                    if v_isSharedCheck_1677_ == 0 {
                        v___x_1650_ = v_b_1633_;
                        v_isShared_1651_ = v_isSharedCheck_1677_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1648_);
                        crate::leanh::lean_inc(v_fst_1647_);
                        crate::leanh::lean_dec(v_b_1633_);
                        v___x_1650_ = crate::leanh::lean_box(0);
                        v_isShared_1651_ = v_isSharedCheck_1677_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1652_ = lean_array_fget_borrowed(v_snd_1648_, v_a_1632_);
                crate::leanh::lean_inc(v___x_1652_);
                v___x_1653_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v___x_1652_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
                if crate::leanh::lean_obj_tag(v___x_1653_) == 0 {
                    v_a_1654_ = crate::leanh::lean_ctor_get(v___x_1653_, 0);
                    crate::leanh::lean_inc(v_a_1654_);
                    crate::leanh::lean_dec_ref_known(v___x_1653_, 1);
                    v___x_1660_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v___x_1652_,
                            v_a_1654_,
                        );
                    if v___x_1660_ == 0 {
                        crate::leanh::lean_dec(v_fst_1647_);
                        v___x_1661_ = lean_array_fset(v_snd_1648_, v_a_1632_, v_a_1654_);
                        v___x_1662_ = crate::leanh::lean_box((v_modified_1645_) as usize);
                        if v_isShared_1651_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1650_, 1, v___x_1661_);
                            crate::leanh::lean_ctor_set(v___x_1650_, 0, v___x_1662_);
                            v___x_1664_ = v___x_1650_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1665_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1661_);
                            v___x_1664_ = v_reuseFailAlloc_1665_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1654_);
                        if v_isShared_1651_ == 0 {
                            v___x_1667_ = v___x_1650_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1668_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_fst_1647_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_snd_1648_);
                            v___x_1667_ = v_reuseFailAlloc_1668_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1650_);
                    crate::leanh::lean_dec(v_snd_1648_);
                    crate::leanh::lean_dec(v_fst_1647_);
                    crate::leanh::lean_dec(v_a_1632_);
                    v_a_1669_ = crate::leanh::lean_ctor_get(v___x_1653_, 0);
                    v_isSharedCheck_1676_ = (!crate::leanh::lean_is_exclusive(v___x_1653_)) as u8;
                    if v_isSharedCheck_1676_ == 0 {
                        v___x_1671_ = v___x_1653_;
                        v_isShared_1672_ = v_isSharedCheck_1676_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1669_);
                        crate::leanh::lean_dec(v___x_1653_);
                        v___x_1671_ = crate::leanh::lean_box(0);
                        v_isShared_1672_ = v_isSharedCheck_1676_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1657_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1658_ = lean_nat_add(v_a_1632_, v___x_1657_);
                crate::leanh::lean_dec(v_a_1632_);
                v_a_1632_ = v___x_1658_;
                v_b_1633_ = v_a_1656_;
                state = 0;
                continue;
            }
            3 => {
                v_a_1656_ = v___x_1664_;
                state = 2;
                continue;
            }
            4 => {
                v_a_1656_ = v___x_1667_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_1672_ == 0 {
                    v___x_1674_ = v___x_1671_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
                    v___x_1674_ = v_reuseFailAlloc_1675_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(
    mut v_e_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: u8,
    mut v_x_1680_: *mut crate::leanh::LeanObject,
    mut v_x_1681_: *mut crate::leanh::LeanObject,
    mut v_x_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
    mut v___y_1687_: *mut crate::leanh::LeanObject,
    mut v___y_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
    mut v___y_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v_fst_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: u8 = 0;
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut v_a_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1680_) == 5 {
                    v_fn_1694_ = crate::leanh::lean_ctor_get(v_x_1680_, 0);
                    crate::leanh::lean_inc_ref(v_fn_1694_);
                    v_arg_1695_ = crate::leanh::lean_ctor_get(v_x_1680_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1695_);
                    crate::leanh::lean_dec_ref_known(v_x_1680_, 2);
                    v___x_1696_ = lean_array_set(v_x_1681_, v_x_1682_, v_arg_1695_);
                    v___x_1697_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1698_ = lean_nat_sub(v_x_1682_, v___x_1697_);
                    crate::leanh::lean_dec(v_x_1682_);
                    v_x_1680_ = v_fn_1694_;
                    v_x_1681_ = v___x_1696_;
                    v_x_1682_ = v___x_1698_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1682_);
                    v___x_1700_ = lean_array_get_size(v_x_1681_);
                    v___x_1701_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1702_ = crate::leanh::lean_box((v_a_1679_) as usize);
                    v___x_1703_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1703_, 0, v___x_1702_);
                    crate::leanh::lean_ctor_set(v___x_1703_, 1, v_x_1681_);
                    v___x_1704_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(v___x_1700_, v___x_1701_, v___x_1703_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
                    if crate::leanh::lean_obj_tag(v___x_1704_) == 0 {
                        v_a_1705_ = crate::leanh::lean_ctor_get(v___x_1704_, 0);
                        v_isSharedCheck_1719_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1704_)) as u8;
                        if v_isSharedCheck_1719_ == 0 {
                            v___x_1707_ = v___x_1704_;
                            v_isShared_1708_ = v_isSharedCheck_1719_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1705_);
                            crate::leanh::lean_dec(v___x_1704_);
                            v___x_1707_ = crate::leanh::lean_box(0);
                            v_isShared_1708_ = v_isSharedCheck_1719_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1680_);
                        crate::leanh::lean_dec_ref(v_e_1678_);
                        v_a_1720_ = crate::leanh::lean_ctor_get(v___x_1704_, 0);
                        v_isSharedCheck_1727_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1704_)) as u8;
                        if v_isSharedCheck_1727_ == 0 {
                            v___x_1722_ = v___x_1704_;
                            v_isShared_1723_ = v_isSharedCheck_1727_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1720_);
                            crate::leanh::lean_dec(v___x_1704_);
                            v___x_1722_ = crate::leanh::lean_box(0);
                            v_isShared_1723_ = v_isSharedCheck_1727_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1709_ = crate::leanh::lean_ctor_get(v_a_1705_, 0);
                v___x_1710_ = (crate::leanh::lean_unbox(v_fst_1709_) as u8);
                if v___x_1710_ == 0 {
                    crate::leanh::lean_dec(v_a_1705_);
                    crate::leanh::lean_dec_ref(v_x_1680_);
                    if v_isShared_1708_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1707_, 0, v_e_1678_);
                        v___x_1712_ = v___x_1707_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1713_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_e_1678_);
                        v___x_1712_ = v_reuseFailAlloc_1713_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1678_);
                    v_snd_1714_ = crate::leanh::lean_ctor_get(v_a_1705_, 1);
                    crate::leanh::lean_inc(v_snd_1714_);
                    crate::leanh::lean_dec(v_a_1705_);
                    v___x_1715_ = l_Lean_mkAppN(v_x_1680_, v_snd_1714_);
                    crate::leanh::lean_dec(v_snd_1714_);
                    if v_isShared_1708_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1707_, 0, v___x_1715_);
                        v___x_1717_ = v___x_1707_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
                        v___x_1717_ = v_reuseFailAlloc_1718_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1712_;
            }
            3 => {
                return v___x_1717_;
            }
            4 => {
                if v_isShared_1723_ == 0 {
                    v___x_1725_ = v___x_1722_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
                    v___x_1725_ = v_reuseFailAlloc_1726_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3___boxed(
    mut v_e_1728_: *mut crate::leanh::LeanObject,
    mut v_a_1729_: *mut crate::leanh::LeanObject,
    mut v_x_1730_: *mut crate::leanh::LeanObject,
    mut v_x_1731_: *mut crate::leanh::LeanObject,
    mut v_x_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
    mut v___y_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
    mut v___y_1741_: *mut crate::leanh::LeanObject,
    mut v___y_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_74556__boxed_1744_: u8 = 0;
    let mut v_res_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_74556__boxed_1744_ = (crate::leanh::lean_unbox(v_a_1729_) as u8);
    v_res_1745_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(v_e_1728_, v_a_74556__boxed_1744_, v_x_1730_, v_x_1731_, v_x_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
    crate::leanh::lean_dec(v___y_1742_);
    crate::leanh::lean_dec_ref(v___y_1741_);
    crate::leanh::lean_dec(v___y_1740_);
    crate::leanh::lean_dec_ref(v___y_1739_);
    crate::leanh::lean_dec(v___y_1738_);
    crate::leanh::lean_dec_ref(v___y_1737_);
    crate::leanh::lean_dec(v___y_1736_);
    crate::leanh::lean_dec_ref(v___y_1735_);
    crate::leanh::lean_dec(v___y_1734_);
    crate::leanh::lean_dec(v___y_1733_);
    return v_res_1745_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg___boxed(
    mut v_upperBound_1746_: *mut crate::leanh::LeanObject,
    mut v_a_1747_: *mut crate::leanh::LeanObject,
    mut v_b_1748_: *mut crate::leanh::LeanObject,
    mut v___y_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
    mut v___y_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
    mut v___y_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1760_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(v_upperBound_1746_, v_a_1747_, v_b_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
    crate::leanh::lean_dec(v___y_1758_);
    crate::leanh::lean_dec_ref(v___y_1757_);
    crate::leanh::lean_dec(v___y_1756_);
    crate::leanh::lean_dec_ref(v___y_1755_);
    crate::leanh::lean_dec(v___y_1754_);
    crate::leanh::lean_dec_ref(v___y_1753_);
    crate::leanh::lean_dec(v___y_1752_);
    crate::leanh::lean_dec_ref(v___y_1751_);
    crate::leanh::lean_dec(v___y_1750_);
    crate::leanh::lean_dec(v___y_1749_);
    crate::leanh::lean_dec(v_upperBound_1746_);
    return v_res_1760_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess___boxed(
    mut v_e_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
    mut v_a_1764_: *mut crate::leanh::LeanObject,
    mut v_a_1765_: *mut crate::leanh::LeanObject,
    mut v_a_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1773_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_e_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
    crate::leanh::lean_dec(v_a_1771_);
    crate::leanh::lean_dec_ref(v_a_1770_);
    crate::leanh::lean_dec(v_a_1769_);
    crate::leanh::lean_dec_ref(v_a_1768_);
    crate::leanh::lean_dec(v_a_1767_);
    crate::leanh::lean_dec_ref(v_a_1766_);
    crate::leanh::lean_dec(v_a_1765_);
    crate::leanh::lean_dec_ref(v_a_1764_);
    crate::leanh::lean_dec(v_a_1763_);
    crate::leanh::lean_dec(v_a_1762_);
    return v_res_1773_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___boxed(
    mut v_e_1774_: *mut crate::leanh::LeanObject,
    mut v_a_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
    mut v_a_1777_: *mut crate::leanh::LeanObject,
    mut v_a_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v_a_1781_: *mut crate::leanh::LeanObject,
    mut v_a_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_e_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
    crate::leanh::lean_dec(v_a_1784_);
    crate::leanh::lean_dec_ref(v_a_1783_);
    crate::leanh::lean_dec(v_a_1782_);
    crate::leanh::lean_dec_ref(v_a_1781_);
    crate::leanh::lean_dec(v_a_1780_);
    crate::leanh::lean_dec_ref(v_a_1779_);
    crate::leanh::lean_dec(v_a_1778_);
    crate::leanh::lean_dec_ref(v_a_1777_);
    crate::leanh::lean_dec(v_a_1776_);
    crate::leanh::lean_dec(v_a_1775_);
    return v_res_1786_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6(
    mut v_e_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
    mut v___y_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg(v_e_1787_, v___y_1795_);
    return v___x_1799_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___boxed(
    mut v_e_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6(v_e_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
    crate::leanh::lean_dec(v___y_1810_);
    crate::leanh::lean_dec_ref(v___y_1809_);
    crate::leanh::lean_dec(v___y_1808_);
    crate::leanh::lean_dec_ref(v___y_1807_);
    crate::leanh::lean_dec(v___y_1806_);
    crate::leanh::lean_dec_ref(v___y_1805_);
    crate::leanh::lean_dec(v___y_1804_);
    crate::leanh::lean_dec_ref(v___y_1803_);
    crate::leanh::lean_dec(v___y_1802_);
    crate::leanh::lean_dec(v___y_1801_);
    return v_res_1812_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0(
    mut v_00_u03b2_1813_: *mut crate::leanh::LeanObject,
    mut v_m_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
    mut v_b_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v_m_1814_, v_a_1815_, v_b_1816_);
    return v___x_1817_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1(
    mut v_00_u03b2_1818_: *mut crate::leanh::LeanObject,
    mut v_m_1819_: *mut crate::leanh::LeanObject,
    mut v_a_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(v_m_1819_, v_a_1820_);
    return v___x_1821_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___boxed(
    mut v_00_u03b2_1822_: *mut crate::leanh::LeanObject,
    mut v_m_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1825_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1(v_00_u03b2_1822_, v_m_1823_, v_a_1824_);
    crate::leanh::lean_dec_ref(v_a_1824_);
    crate::leanh::lean_dec_ref(v_m_1823_);
    return v_res_1825_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2(
    mut v_upperBound_1826_: *mut crate::leanh::LeanObject,
    mut v___x_1827_: *mut crate::leanh::LeanObject,
    mut v_inst_1828_: *mut crate::leanh::LeanObject,
    mut v_R_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
    mut v_b_1831_: *mut crate::leanh::LeanObject,
    mut v_c_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
    mut v___y_1834_: *mut crate::leanh::LeanObject,
    mut v___y_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1844_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(v_upperBound_1826_, v_a_1830_, v_b_1831_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
    return v___x_1844_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_1845_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_1846_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_1847_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_R_1848_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_1849_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_1850_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_c_1851_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_1852_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_1853_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_1854_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_1855_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_1856_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1857_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1858_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1859_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1860_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1861_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_1862_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1863_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2(v_upperBound_1845_, v___x_1846_, v_inst_1847_, v_R_1848_, v_a_1849_, v_b_1850_, v_c_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
    crate::leanh::lean_dec(v___y_1861_);
    crate::leanh::lean_dec_ref(v___y_1860_);
    crate::leanh::lean_dec(v___y_1859_);
    crate::leanh::lean_dec_ref(v___y_1858_);
    crate::leanh::lean_dec(v___y_1857_);
    crate::leanh::lean_dec_ref(v___y_1856_);
    crate::leanh::lean_dec(v___y_1855_);
    crate::leanh::lean_dec_ref(v___y_1854_);
    crate::leanh::lean_dec(v___y_1853_);
    crate::leanh::lean_dec(v___y_1852_);
    crate::leanh::lean_dec(v___x_1846_);
    crate::leanh::lean_dec(v_upperBound_1845_);
    return v_res_1863_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0(
    mut v_00_u03b2_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_x_1866_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1867_: u8 = 0;
    v___x_1867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg(v_a_1865_, v_x_1866_);
    return v___x_1867_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___boxed(
    mut v_00_u03b2_1868_: *mut crate::leanh::LeanObject,
    mut v_a_1869_: *mut crate::leanh::LeanObject,
    mut v_x_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1871_: u8 = 0;
    let mut v_r_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0(v_00_u03b2_1868_, v_a_1869_, v_x_1870_);
    crate::leanh::lean_dec(v_x_1870_);
    crate::leanh::lean_dec_ref(v_a_1869_);
    v_r_1872_ = crate::leanh::lean_box((v_res_1871_) as usize);
    return v_r_1872_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1(
    mut v_00_u03b2_1873_: *mut crate::leanh::LeanObject,
    mut v_data_1874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1___redArg(v_data_1874_);
    return v___x_1875_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2(
    mut v_00_u03b2_1876_: *mut crate::leanh::LeanObject,
    mut v_a_1877_: *mut crate::leanh::LeanObject,
    mut v_b_1878_: *mut crate::leanh::LeanObject,
    mut v_x_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1880_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(v_a_1877_, v_b_1878_, v_x_1879_);
    return v___x_1880_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4(
    mut v_00_u03b2_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_x_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1884_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg(v_a_1882_, v_x_1883_);
    return v___x_1884_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___boxed(
    mut v_00_u03b2_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
    mut v_x_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1888_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4(v_00_u03b2_1885_, v_a_1886_, v_x_1887_);
    crate::leanh::lean_dec(v_x_1887_);
    crate::leanh::lean_dec_ref(v_a_1886_);
    return v_res_1888_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5(
    mut v_00_u03b2_1889_: *mut crate::leanh::LeanObject,
    mut v_i_1890_: *mut crate::leanh::LeanObject,
    mut v_source_1891_: *mut crate::leanh::LeanObject,
    mut v_target_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5___redArg(v_i_1890_, v_source_1891_, v_target_1892_);
    return v___x_1893_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9(
    mut v_00_u03b2_1894_: *mut crate::leanh::LeanObject,
    mut v_x_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9___redArg(v_x_1895_, v_x_1896_);
    return v___x_1897_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(
    mut v_category_1898_: *mut crate::leanh::LeanObject,
    mut v_opts_1899_: *mut crate::leanh::LeanObject,
    mut v_act_1900_: *mut crate::leanh::LeanObject,
    mut v_decl_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
    mut v___y_1910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1910_);
    crate::leanh::lean_inc_ref(v___y_1909_);
    crate::leanh::lean_inc(v___y_1908_);
    crate::leanh::lean_inc_ref(v___y_1907_);
    crate::leanh::lean_inc(v___y_1906_);
    crate::leanh::lean_inc_ref(v___y_1905_);
    crate::leanh::lean_inc(v___y_1904_);
    crate::leanh::lean_inc_ref(v___y_1903_);
    crate::leanh::lean_inc(v___y_1902_);
    v___x_1912_ = crate::leanh::lean_apply_9(
        v_act_1900_,
        v___y_1902_,
        v___y_1903_,
        v___y_1904_,
        v___y_1905_,
        v___y_1906_,
        v___y_1907_,
        v___y_1908_,
        v___y_1909_,
        v___y_1910_,
    );
    v___x_1913_ = l_Lean_profileitIOUnsafe___redArg(
        v_category_1898_,
        v_opts_1899_,
        v___x_1912_,
        v_decl_1901_,
    );
    return v___x_1913_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg___boxed(
    mut v_category_1914_: *mut crate::leanh::LeanObject,
    mut v_opts_1915_: *mut crate::leanh::LeanObject,
    mut v_act_1916_: *mut crate::leanh::LeanObject,
    mut v_decl_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1928_ =
        l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(
            v_category_1914_,
            v_opts_1915_,
            v_act_1916_,
            v_decl_1917_,
            v___y_1918_,
            v___y_1919_,
            v___y_1920_,
            v___y_1921_,
            v___y_1922_,
            v___y_1923_,
            v___y_1924_,
            v___y_1925_,
            v___y_1926_,
        );
    crate::leanh::lean_dec(v___y_1926_);
    crate::leanh::lean_dec_ref(v___y_1925_);
    crate::leanh::lean_dec(v___y_1924_);
    crate::leanh::lean_dec_ref(v___y_1923_);
    crate::leanh::lean_dec(v___y_1922_);
    crate::leanh::lean_dec_ref(v___y_1921_);
    crate::leanh::lean_dec(v___y_1920_);
    crate::leanh::lean_dec_ref(v___y_1919_);
    crate::leanh::lean_dec(v___y_1918_);
    crate::leanh::lean_dec_ref(v_opts_1915_);
    crate::leanh::lean_dec_ref(v_category_1914_);
    return v_res_1928_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0(
    mut v_00_u03b1_1929_: *mut crate::leanh::LeanObject,
    mut v_category_1930_: *mut crate::leanh::LeanObject,
    mut v_opts_1931_: *mut crate::leanh::LeanObject,
    mut v_act_1932_: *mut crate::leanh::LeanObject,
    mut v_decl_1933_: *mut crate::leanh::LeanObject,
    mut v___y_1934_: *mut crate::leanh::LeanObject,
    mut v___y_1935_: *mut crate::leanh::LeanObject,
    mut v___y_1936_: *mut crate::leanh::LeanObject,
    mut v___y_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ =
        l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(
            v_category_1930_,
            v_opts_1931_,
            v_act_1932_,
            v_decl_1933_,
            v___y_1934_,
            v___y_1935_,
            v___y_1936_,
            v___y_1937_,
            v___y_1938_,
            v___y_1939_,
            v___y_1940_,
            v___y_1941_,
            v___y_1942_,
        );
    return v___x_1944_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___boxed(
    mut v_00_u03b1_1945_: *mut crate::leanh::LeanObject,
    mut v_category_1946_: *mut crate::leanh::LeanObject,
    mut v_opts_1947_: *mut crate::leanh::LeanObject,
    mut v_act_1948_: *mut crate::leanh::LeanObject,
    mut v_decl_1949_: *mut crate::leanh::LeanObject,
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
    mut v___y_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0(
        v_00_u03b1_1945_,
        v_category_1946_,
        v_opts_1947_,
        v_act_1948_,
        v_decl_1949_,
        v___y_1950_,
        v___y_1951_,
        v___y_1952_,
        v___y_1953_,
        v___y_1954_,
        v___y_1955_,
        v___y_1956_,
        v___y_1957_,
        v___y_1958_,
    );
    crate::leanh::lean_dec(v___y_1958_);
    crate::leanh::lean_dec_ref(v___y_1957_);
    crate::leanh::lean_dec(v___y_1956_);
    crate::leanh::lean_dec_ref(v___y_1955_);
    crate::leanh::lean_dec(v___y_1954_);
    crate::leanh::lean_dec_ref(v___y_1953_);
    crate::leanh::lean_dec(v___y_1952_);
    crate::leanh::lean_dec_ref(v___y_1951_);
    crate::leanh::lean_dec(v___y_1950_);
    crate::leanh::lean_dec_ref(v_opts_1947_);
    crate::leanh::lean_dec_ref(v_category_1946_);
    return v_res_1960_;
}
pub unsafe fn l_Lean_Meta_Grind_markNestedSubsingletons___lam__0(
    mut v___x_1961_: *mut crate::leanh::LeanObject,
    mut v_e_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
    mut v___y_1968_: *mut crate::leanh::LeanObject,
    mut v___y_1969_: *mut crate::leanh::LeanObject,
    mut v___y_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1973_ = lean_st_mk_ref(v___x_1961_);
                v___x_1974_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_e_1962_, v___x_1973_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
                if crate::leanh::lean_obj_tag(v___x_1974_) == 0 {
                    v_a_1975_ = crate::leanh::lean_ctor_get(v___x_1974_, 0);
                    v_isSharedCheck_1983_ = (!crate::leanh::lean_is_exclusive(v___x_1974_)) as u8;
                    if v_isSharedCheck_1983_ == 0 {
                        v___x_1977_ = v___x_1974_;
                        v_isShared_1978_ = v_isSharedCheck_1983_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1975_);
                        crate::leanh::lean_dec(v___x_1974_);
                        v___x_1977_ = crate::leanh::lean_box(0);
                        v_isShared_1978_ = v_isSharedCheck_1983_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1973_);
                    return v___x_1974_;
                }
            }
            1 => {
                v___x_1979_ = lean_st_ref_get(v___x_1973_);
                crate::leanh::lean_dec(v___x_1973_);
                crate::leanh::lean_dec(v___x_1979_);
                if v_isShared_1978_ == 0 {
                    v___x_1981_ = v___x_1977_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1975_);
                    v___x_1981_ = v_reuseFailAlloc_1982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_markNestedSubsingletons___lam__0___boxed(
    mut v___x_1984_: *mut crate::leanh::LeanObject,
    mut v_e_1985_: *mut crate::leanh::LeanObject,
    mut v___y_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1996_ = l_Lean_Meta_Grind_markNestedSubsingletons___lam__0(
        v___x_1984_,
        v_e_1985_,
        v___y_1986_,
        v___y_1987_,
        v___y_1988_,
        v___y_1989_,
        v___y_1990_,
        v___y_1991_,
        v___y_1992_,
        v___y_1993_,
        v___y_1994_,
    );
    crate::leanh::lean_dec(v___y_1994_);
    crate::leanh::lean_dec_ref(v___y_1993_);
    crate::leanh::lean_dec(v___y_1992_);
    crate::leanh::lean_dec_ref(v___y_1991_);
    crate::leanh::lean_dec(v___y_1990_);
    crate::leanh::lean_dec_ref(v___y_1989_);
    crate::leanh::lean_dec(v___y_1988_);
    crate::leanh::lean_dec_ref(v___y_1987_);
    crate::leanh::lean_dec(v___y_1986_);
    return v_res_1996_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1998_ = crate::leanh::lean_box(0);
    v___x_1999_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2000_ = lean_mk_array(v___x_1999_, v___x_1998_);
    return v___x_2000_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markNestedSubsingletons___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markNestedSubsingletons___closed__1_once),
        _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__1,
    );
    v___x_2002_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2003_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2003_, 0, v___x_2002_);
    crate::leanh::lean_ctor_set(v___x_2003_, 1, v___x_2001_);
    return v___x_2003_;
}
pub unsafe fn l_Lean_Meta_Grind_markNestedSubsingletons(
    mut v_e_2004_: *mut crate::leanh::LeanObject,
    mut v_a_2005_: *mut crate::leanh::LeanObject,
    mut v_a_2006_: *mut crate::leanh::LeanObject,
    mut v_a_2007_: *mut crate::leanh::LeanObject,
    mut v_a_2008_: *mut crate::leanh::LeanObject,
    mut v_a_2009_: *mut crate::leanh::LeanObject,
    mut v_a_2010_: *mut crate::leanh::LeanObject,
    mut v_a_2011_: *mut crate::leanh::LeanObject,
    mut v_a_2012_: *mut crate::leanh::LeanObject,
    mut v_a_2013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_2015_ = crate::leanh::lean_ctor_get(v_a_2012_, 2);
    v___x_2016_ = l_Lean_Meta_Grind_markNestedSubsingletons___closed__0;
    v___x_2017_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markNestedSubsingletons___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markNestedSubsingletons___closed__2_once),
        _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__2,
    );
    v___f_2018_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_markNestedSubsingletons___lam__0___boxed as *mut core::ffi::c_void,
        12,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2018_, 0, v___x_2017_);
    crate::leanh::lean_closure_set(v___f_2018_, 1, v_e_2004_);
    v___x_2019_ = crate::leanh::lean_box(0);
    v___x_2020_ =
        l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(
            v___x_2016_,
            v_options_2015_,
            v___f_2018_,
            v___x_2019_,
            v_a_2005_,
            v_a_2006_,
            v_a_2007_,
            v_a_2008_,
            v_a_2009_,
            v_a_2010_,
            v_a_2011_,
            v_a_2012_,
            v_a_2013_,
        );
    return v___x_2020_;
}
pub unsafe fn l_Lean_Meta_Grind_markNestedSubsingletons___boxed(
    mut v_e_2021_: *mut crate::leanh::LeanObject,
    mut v_a_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
    mut v_a_2025_: *mut crate::leanh::LeanObject,
    mut v_a_2026_: *mut crate::leanh::LeanObject,
    mut v_a_2027_: *mut crate::leanh::LeanObject,
    mut v_a_2028_: *mut crate::leanh::LeanObject,
    mut v_a_2029_: *mut crate::leanh::LeanObject,
    mut v_a_2030_: *mut crate::leanh::LeanObject,
    mut v_a_2031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2032_ = l_Lean_Meta_Grind_markNestedSubsingletons(
        v_e_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_,
        v_a_2029_, v_a_2030_,
    );
    crate::leanh::lean_dec(v_a_2030_);
    crate::leanh::lean_dec_ref(v_a_2029_);
    crate::leanh::lean_dec(v_a_2028_);
    crate::leanh::lean_dec_ref(v_a_2027_);
    crate::leanh::lean_dec(v_a_2026_);
    crate::leanh::lean_dec_ref(v_a_2025_);
    crate::leanh::lean_dec(v_a_2024_);
    crate::leanh::lean_dec_ref(v_a_2023_);
    crate::leanh::lean_dec(v_a_2022_);
    return v_res_2032_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(
    mut v_e_2033_: *mut crate::leanh::LeanObject,
    mut v_a_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
    mut v_a_2036_: *mut crate::leanh::LeanObject,
    mut v_a_2037_: *mut crate::leanh::LeanObject,
    mut v_a_2038_: *mut crate::leanh::LeanObject,
    mut v_a_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
    mut v_a_2041_: *mut crate::leanh::LeanObject,
    mut v_a_2042_: *mut crate::leanh::LeanObject,
    mut v_a_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2043_);
                crate::leanh::lean_inc_ref(v_a_2042_);
                crate::leanh::lean_inc(v_a_2041_);
                crate::leanh::lean_inc_ref(v_a_2040_);
                crate::leanh::lean_inc_ref(v_e_2033_);
                v___x_2045_ =
                    lean_infer_type(v_e_2033_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
                if crate::leanh::lean_obj_tag(v___x_2045_) == 0 {
                    v_a_2046_ = crate::leanh::lean_ctor_get(v___x_2045_, 0);
                    crate::leanh::lean_inc(v_a_2046_);
                    crate::leanh::lean_dec_ref_known(v___x_2045_, 1);
                    v___x_2047_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_a_2046_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
                    if crate::leanh::lean_obj_tag(v___x_2047_) == 0 {
                        v_a_2048_ = crate::leanh::lean_ctor_get(v___x_2047_, 0);
                        v_isSharedCheck_2057_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2047_)) as u8;
                        if v_isSharedCheck_2057_ == 0 {
                            v___x_2050_ = v___x_2047_;
                            v_isShared_2051_ = v_isSharedCheck_2057_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2048_);
                            crate::leanh::lean_dec(v___x_2047_);
                            v___x_2050_ = crate::leanh::lean_box(0);
                            v_isShared_2051_ = v_isSharedCheck_2057_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2033_);
                        return v___x_2047_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2033_);
                    return v___x_2045_;
                }
            }
            1 => {
                v___x_2052_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6);
                v___x_2053_ = l_Lean_mkAppB(v___x_2052_, v_a_2048_, v_e_2033_);
                if v_isShared_2051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2050_, 0, v___x_2053_);
                    v___x_2055_ = v___x_2050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
                    v___x_2055_ = v_reuseFailAlloc_2056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof___boxed(
    mut v_e_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
    mut v_a_2065_: *mut crate::leanh::LeanObject,
    mut v_a_2066_: *mut crate::leanh::LeanObject,
    mut v_a_2067_: *mut crate::leanh::LeanObject,
    mut v_a_2068_: *mut crate::leanh::LeanObject,
    mut v_a_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2070_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(v_e_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
    crate::leanh::lean_dec(v_a_2068_);
    crate::leanh::lean_dec_ref(v_a_2067_);
    crate::leanh::lean_dec(v_a_2066_);
    crate::leanh::lean_dec_ref(v_a_2065_);
    crate::leanh::lean_dec(v_a_2064_);
    crate::leanh::lean_dec_ref(v_a_2063_);
    crate::leanh::lean_dec(v_a_2062_);
    crate::leanh::lean_dec_ref(v_a_2061_);
    crate::leanh::lean_dec(v_a_2060_);
    crate::leanh::lean_dec(v_a_2059_);
    return v_res_2070_;
}
pub unsafe fn l_Lean_Meta_Grind_markProof(
    mut v_e_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
    mut v_a_2073_: *mut crate::leanh::LeanObject,
    mut v_a_2074_: *mut crate::leanh::LeanObject,
    mut v_a_2075_: *mut crate::leanh::LeanObject,
    mut v_a_2076_: *mut crate::leanh::LeanObject,
    mut v_a_2077_: *mut crate::leanh::LeanObject,
    mut v_a_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2082_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3;
                v___x_2083_ = l_Lean_Expr_isAppOf(v_e_2071_, v___x_2082_);
                if v___x_2083_ == 0 {
                    v___x_2084_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_markNestedSubsingletons___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_markNestedSubsingletons___closed__2_once
                        ),
                        _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__2,
                    );
                    v___x_2085_ = lean_st_mk_ref(v___x_2084_);
                    v___x_2086_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(v_e_2071_, v___x_2085_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
                    if crate::leanh::lean_obj_tag(v___x_2086_) == 0 {
                        v_a_2087_ = crate::leanh::lean_ctor_get(v___x_2086_, 0);
                        v_isSharedCheck_2095_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2086_)) as u8;
                        if v_isSharedCheck_2095_ == 0 {
                            v___x_2089_ = v___x_2086_;
                            v_isShared_2090_ = v_isSharedCheck_2095_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2087_);
                            crate::leanh::lean_dec(v___x_2086_);
                            v___x_2089_ = crate::leanh::lean_box(0);
                            v_isShared_2090_ = v_isSharedCheck_2095_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2085_);
                        return v___x_2086_;
                    }
                } else {
                    v___x_2096_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2096_, 0, v_e_2071_);
                    return v___x_2096_;
                }
            }
            1 => {
                v___x_2091_ = lean_st_ref_get(v___x_2085_);
                crate::leanh::lean_dec(v___x_2085_);
                crate::leanh::lean_dec(v___x_2091_);
                if v_isShared_2090_ == 0 {
                    v___x_2093_ = v___x_2089_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2094_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2087_);
                    v___x_2093_ = v_reuseFailAlloc_2094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_markProof___boxed(
    mut v_e_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
    mut v_a_2104_: *mut crate::leanh::LeanObject,
    mut v_a_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Lean_Meta_Grind_markProof(
        v_e_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_,
        v_a_2105_, v_a_2106_,
    );
    crate::leanh::lean_dec(v_a_2106_);
    crate::leanh::lean_dec_ref(v_a_2105_);
    crate::leanh::lean_dec(v_a_2104_);
    crate::leanh::lean_dec_ref(v_a_2103_);
    crate::leanh::lean_dec(v_a_2102_);
    crate::leanh::lean_dec_ref(v_a_2101_);
    crate::leanh::lean_dec(v_a_2100_);
    crate::leanh::lean_dec_ref(v_a_2099_);
    crate::leanh::lean_dec(v_a_2098_);
    return v_res_2108_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
}
