// Lean compiler output
// Module: Lean.Meta.HaveTelescope
// Imports: Lean.Meta.Basic Lean.Meta.MonadSimp Lean.Util.CollectFVars Lean.Util.CollectLooseBVars Lean.Meta.AppBuilder Init.While
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_abstract, lean_expr_eqv,
    lean_expr_has_loose_bvar, lean_expr_instantiate_rev, lean_expr_lower_loose_bvars,
    lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg, l_StateRefT_x27_instMonadFunctor___aux__1___boxed,
    l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override,
    l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadFunctor___lam__0, l_ReaderT_instMonadLift___lam__0___boxed,
    l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadQuotationCoreM, l_Lean_Core_instMonadTraceCoreM,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_isApp,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_letE___override,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp6, l_Lean_mkApp8, l_Lean_mkAppB,
    l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkLambda,
};
use crate::r#gen::Lean::Level::l_Lean_Level_param___override;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_addDecl, l_Lean_LocalDecl_toExpr, l_Lean_LocalDecl_type,
    l_Lean_LocalDecl_value, l_Lean_instInhabitedLocalDecl_default,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkExpectedPropHint,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l_Lean_FVarId_getDecl___redArg, l_Lean_Meta_instAddMessageContextMetaM,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_mkLetFVars, l_Lean_Meta_withExistingLocalDecls___redArg,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_getLevel, l_Lean_Meta_getLevel___boxed};
use crate::r#gen::Lean::Meta::MonadSimp::{
    initialize_Lean_Meta_MonadSimp, runtime_initialize_Lean_Meta_MonadSimp,
};
use crate::r#gen::Lean::Util::CollectFVars::{
    initialize_Lean_Util_CollectFVars, l_Lean_collectFVars,
    runtime_initialize_Lean_Util_CollectFVars,
};
use crate::r#gen::Lean::Util::CollectLooseBVars::{
    initialize_Lean_Util_CollectLooseBVars, l_Lean_Expr_collectLooseBVars,
    runtime_initialize_Lean_Util_CollectLooseBVars,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_addTrace___redArg,
    l_Lean_instMonadTraceOfMonadLift___redArg,
};
static mut l_Lean_Meta_instInhabitedHaveInfo_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedHaveInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedHaveInfo_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedHaveInfo_default___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedHaveInfo_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedHaveInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedHaveInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0_value:
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
static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        95, 104, 97, 118, 101, 95, 116, 101, 108, 101, 115, 99, 111, 112, 101, 95, 105, 110, 102,
        111, 95, 100, 117, 109, 109, 121, 95, 0,
    ],
};
static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1_value)
            as *mut crate::leanh::LeanObject,
        14057379391456668678 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedHaveTelescopeInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0_value:
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
static mut l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedSimpHaveResult_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 101, 102, 108, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13480818501600609864 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 100, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,6041859491766292191 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [104, 97, 118, 101, 95, 117, 110, 117, 115, 101, 100, 95, 100, 101, 112, 39, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [104, 97, 118, 101, 95, 117, 110, 117, 115, 101, 100, 39, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [104, 97, 118, 101, 95, 98, 111, 100, 121, 95, 99, 111, 110, 103, 114, 95, 100, 101, 112, 39, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [104, 97, 118, 101, 95, 118, 97, 108, 95, 99, 111, 110, 103, 114, 39, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [104, 97, 118, 101, 95, 98, 111, 100, 121, 95, 99, 111, 110, 103, 114, 39, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 97, 118, 101, 95, 99, 111, 110, 103, 114, 39, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [104, 97, 118, 101, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 59, 32, 115, 105, 109, 112, 108, 105, 102, 121, 105, 110, 103, 32, 98, 111, 100, 121, 32, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8_value) as *mut crate::leanh::LeanObject,8887549148216994784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,13650486229248665291 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject,584327297260857319 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [104, 97, 118, 101, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 59, 32, 117, 110, 117, 115, 101, 100, 32, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [104, 97, 118, 101, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 59, 32, 102, 105, 120, 101, 100, 32, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 61, 62, 32, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [104, 97, 118, 101, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 59, 32, 110, 111, 110, 45, 102, 105, 120, 101, 100, 32, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [68, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value) as *mut crate::leanh::LeanObject,976856721057904807 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__5_value) as *mut crate::leanh::LeanObject,11531678945225641079 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__6_value) as *mut crate::leanh::LeanObject,9556918813098452982 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__7_value) as *mut crate::leanh::LeanObject,14987375182540660802 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10_value) as *mut crate::leanh::LeanObject,16031313106467345919 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,16084188049149197294 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11_value) as *mut crate::leanh::LeanObject,3381932731117151009 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 72, 97, 118, 101, 84, 101, 108, 101, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4_value: crate::leanh::LeanStringObject<66> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 66, m_capacity: 66, m_length: 65, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 72, 97, 118, 101, 84, 101, 108, 101, 115, 99, 111, 112, 101, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 115, 105, 109, 112, 72, 97, 118, 101, 84, 101, 108, 101, 115, 99, 111, 112, 101, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5_value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 33, 114, 98, 46, 101, 120, 112, 114, 84, 121, 112, 101, 46, 104, 97, 115, 76, 111, 111, 115, 101, 66, 86, 97, 114, 32, 48, 10, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [95, 115, 105, 109, 112, 95, 108, 101, 116, 95, 117, 110, 117, 115, 101, 100, 95, 100, 117, 109, 109, 121, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value) as *mut crate::leanh::LeanObject,7393802624243764355 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__0_value) as *mut crate::leanh::LeanObject,17532416664988428445 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 115, 105, 109, 112, 72, 97, 118, 101, 84, 101,
        108, 101, 115, 99, 111, 112, 101, 0,
    ],
};
static mut l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1_value:
    crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 33, 105, 110, 102, 111, 46, 104, 97, 118, 101, 73, 110, 102, 111, 46, 105, 115, 69,
        109, 112, 116, 121, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2555_ = crate::leanh::lean_box(0);
    v___x_2556_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2557_ = lean_mk_array(v___x_2556_, v___x_2555_);
    return v___x_2557_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2558_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__0_once),
        _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__0,
    );
    v___x_2559_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2560_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2560_, 0, v___x_2559_);
    crate::leanh::lean_ctor_set(v___x_2560_, 1, v___x_2558_);
    return v___x_2560_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2561_ = crate::leanh::lean_box(0);
    v___x_2562_ = l_Lean_instInhabitedLocalDecl_default;
    v___x_2563_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once),
        _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1,
    );
    v___x_2564_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2563_);
    crate::leanh::lean_ctor_set(v___x_2564_, 1, v___x_2563_);
    crate::leanh::lean_ctor_set(v___x_2564_, 2, v___x_2562_);
    crate::leanh::lean_ctor_set(v___x_2564_, 3, v___x_2561_);
    return v___x_2564_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveInfo_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2565_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__2_once),
        _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__2,
    );
    return v___x_2565_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = l_Lean_Meta_instInhabitedHaveInfo_default;
    return v___x_2566_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2572_ = crate::leanh::lean_box(0);
    v___x_2573_ = l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2;
    v___x_2574_ = l_Lean_Expr_const___override(v___x_2573_, v___x_2572_);
    return v___x_2574_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2575_ = l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2;
    v___x_2576_ = l_Lean_Level_param___override(v___x_2575_);
    return v___x_2576_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2577_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4_once
        ),
        _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4,
    );
    v___x_2578_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3_once
        ),
        _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3,
    );
    v___x_2579_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once),
        _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1,
    );
    v___x_2580_ = l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0;
    v___x_2581_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2581_, 0, v___x_2580_);
    crate::leanh::lean_ctor_set(v___x_2581_, 1, v___x_2579_);
    crate::leanh::lean_ctor_set(v___x_2581_, 2, v___x_2579_);
    crate::leanh::lean_ctor_set(v___x_2581_, 3, v___x_2578_);
    crate::leanh::lean_ctor_set(v___x_2581_, 4, v___x_2578_);
    crate::leanh::lean_ctor_set(v___x_2581_, 5, v___x_2577_);
    return v___x_2581_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2582_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once
        ),
        _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5,
    );
    return v___x_2582_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2583_ = l_Lean_Meta_instInhabitedHaveTelescopeInfo_default;
    return v___x_2583_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(
    mut v_lctx_2584_: *mut crate::leanh::LeanObject,
    mut v_x_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
    mut v___y_2587_: *mut crate::leanh::LeanObject,
    mut v___y_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyedConfig_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_2592_: u8 = 0;
    let mut v_zetaDeltaSet_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2598_: u8 = 0;
    let mut v_inTypeClassResolution_2599_: u8 = 0;
    let mut v_cacheInferType_2600_: u8 = 0;
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyedConfig_2591_ = crate::leanh::lean_ctor_get(v___y_2586_, 0);
    v_trackZetaDelta_2592_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2586_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
    );
    v_zetaDeltaSet_2593_ = crate::leanh::lean_ctor_get(v___y_2586_, 1);
    v_localInstances_2594_ = crate::leanh::lean_ctor_get(v___y_2586_, 3);
    v_defEqCtx_x3f_2595_ = crate::leanh::lean_ctor_get(v___y_2586_, 4);
    v_synthPendingDepth_2596_ = crate::leanh::lean_ctor_get(v___y_2586_, 5);
    v_canUnfold_x3f_2597_ = crate::leanh::lean_ctor_get(v___y_2586_, 6);
    v_univApprox_2598_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2586_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
    );
    v_inTypeClassResolution_2599_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2586_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
    );
    v_cacheInferType_2600_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2586_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
    );
    crate::leanh::lean_inc(v_canUnfold_x3f_2597_);
    crate::leanh::lean_inc(v_synthPendingDepth_2596_);
    crate::leanh::lean_inc(v_defEqCtx_x3f_2595_);
    crate::leanh::lean_inc_ref(v_localInstances_2594_);
    crate::leanh::lean_inc(v_zetaDeltaSet_2593_);
    crate::leanh::lean_inc_ref(v_keyedConfig_2591_);
    v___x_2601_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_2601_, 0, v_keyedConfig_2591_);
    crate::leanh::lean_ctor_set(v___x_2601_, 1, v_zetaDeltaSet_2593_);
    crate::leanh::lean_ctor_set(v___x_2601_, 2, v_lctx_2584_);
    crate::leanh::lean_ctor_set(v___x_2601_, 3, v_localInstances_2594_);
    crate::leanh::lean_ctor_set(v___x_2601_, 4, v_defEqCtx_x3f_2595_);
    crate::leanh::lean_ctor_set(v___x_2601_, 5, v_synthPendingDepth_2596_);
    crate::leanh::lean_ctor_set(v___x_2601_, 6, v_canUnfold_x3f_2597_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2601_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v_trackZetaDelta_2592_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2601_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v_univApprox_2598_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2601_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v_inTypeClassResolution_2599_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2601_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v_cacheInferType_2600_,
    );
    crate::leanh::lean_inc(v___y_2589_);
    crate::leanh::lean_inc_ref(v___y_2588_);
    crate::leanh::lean_inc(v___y_2587_);
    v___x_2602_ = crate::leanh::lean_apply_5(
        v_x_2585_,
        v___x_2601_,
        v___y_2587_,
        v___y_2588_,
        v___y_2589_,
        crate::leanh::lean_box(0),
    );
    return v___x_2602_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg___boxed(
    mut v_lctx_2603_: *mut crate::leanh::LeanObject,
    mut v_x_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
    mut v___y_2606_: *mut crate::leanh::LeanObject,
    mut v___y_2607_: *mut crate::leanh::LeanObject,
    mut v___y_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2610_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_2603_, v_x_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
    crate::leanh::lean_dec(v___y_2608_);
    crate::leanh::lean_dec_ref(v___y_2607_);
    crate::leanh::lean_dec(v___y_2606_);
    crate::leanh::lean_dec_ref(v___y_2605_);
    return v_res_2610_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(
    mut v_00_u03b1_2611_: *mut crate::leanh::LeanObject,
    mut v_lctx_2612_: *mut crate::leanh::LeanObject,
    mut v_x_2613_: *mut crate::leanh::LeanObject,
    mut v___y_2614_: *mut crate::leanh::LeanObject,
    mut v___y_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2619_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_2612_, v_x_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
    return v___x_2619_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___boxed(
    mut v_00_u03b1_2620_: *mut crate::leanh::LeanObject,
    mut v_lctx_2621_: *mut crate::leanh::LeanObject,
    mut v_x_2622_: *mut crate::leanh::LeanObject,
    mut v___y_2623_: *mut crate::leanh::LeanObject,
    mut v___y_2624_: *mut crate::leanh::LeanObject,
    mut v___y_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2628_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(v_00_u03b1_2620_, v_lctx_2621_, v_x_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
    crate::leanh::lean_dec(v___y_2626_);
    crate::leanh::lean_dec_ref(v___y_2625_);
    crate::leanh::lean_dec(v___y_2624_);
    crate::leanh::lean_dec_ref(v___y_2623_);
    return v_res_2628_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(
    mut v_x_2629_: *mut crate::leanh::LeanObject,
    mut v_x_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2636_: u8 = 0;
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: u64 = 0;
    let mut v___x_2639_: u64 = 0;
    let mut v___x_2640_: u64 = 0;
    let mut v_fold_2641_: u64 = 0;
    let mut v___x_2642_: u64 = 0;
    let mut v___x_2643_: u64 = 0;
    let mut v___x_2644_: u64 = 0;
    let mut v___x_2645_: usize = 0;
    let mut v___x_2646_: usize = 0;
    let mut v___x_2647_: usize = 0;
    let mut v___x_2648_: usize = 0;
    let mut v___x_2649_: usize = 0;
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2630_) == 0 {
                    return v_x_2629_;
                } else {
                    v_key_2631_ = crate::leanh::lean_ctor_get(v_x_2630_, 0);
                    v_value_2632_ = crate::leanh::lean_ctor_get(v_x_2630_, 1);
                    v_tail_2633_ = crate::leanh::lean_ctor_get(v_x_2630_, 2);
                    v_isSharedCheck_2656_ = (!crate::leanh::lean_is_exclusive(v_x_2630_)) as u8;
                    if v_isSharedCheck_2656_ == 0 {
                        v___x_2635_ = v_x_2630_;
                        v_isShared_2636_ = v_isSharedCheck_2656_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2633_);
                        crate::leanh::lean_inc(v_value_2632_);
                        crate::leanh::lean_inc(v_key_2631_);
                        crate::leanh::lean_dec(v_x_2630_);
                        v___x_2635_ = crate::leanh::lean_box(0);
                        v_isShared_2636_ = v_isSharedCheck_2656_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2637_ = lean_array_get_size(v_x_2629_);
                v___x_2638_ = lean_uint64_of_nat(v_key_2631_);
                v___x_2639_ = 32u64;
                v___x_2640_ = lean_uint64_shift_right(v___x_2638_, v___x_2639_);
                v_fold_2641_ = lean_uint64_xor(v___x_2638_, v___x_2640_);
                v___x_2642_ = 16u64;
                v___x_2643_ = lean_uint64_shift_right(v_fold_2641_, v___x_2642_);
                v___x_2644_ = lean_uint64_xor(v_fold_2641_, v___x_2643_);
                v___x_2645_ = lean_uint64_to_usize(v___x_2644_);
                v___x_2646_ = lean_usize_of_nat(v___x_2637_);
                v___x_2647_ = 1usize;
                v___x_2648_ = lean_usize_sub(v___x_2646_, v___x_2647_);
                v___x_2649_ = lean_usize_land(v___x_2645_, v___x_2648_);
                v___x_2650_ = lean_array_uget_borrowed(v_x_2629_, v___x_2649_);
                crate::leanh::lean_inc(v___x_2650_);
                if v_isShared_2636_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2635_, 2, v___x_2650_);
                    v___x_2652_ = v___x_2635_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2655_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_key_2631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_value_2632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 2, v___x_2650_);
                    v___x_2652_ = v_reuseFailAlloc_2655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2653_ = lean_array_uset(v_x_2629_, v___x_2649_, v___x_2652_);
                v_x_2629_ = v___x_2653_;
                v_x_2630_ = v_tail_2633_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(
    mut v_i_2657_: *mut crate::leanh::LeanObject,
    mut v_source_2658_: *mut crate::leanh::LeanObject,
    mut v_target_2659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: u8 = 0;
    let mut v_es_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2660_ = lean_array_get_size(v_source_2658_);
                v___x_2661_ = lean_nat_dec_lt(v_i_2657_, v___x_2660_);
                if v___x_2661_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2658_);
                    crate::leanh::lean_dec(v_i_2657_);
                    return v_target_2659_;
                } else {
                    v_es_2662_ = lean_array_fget(v_source_2658_, v_i_2657_);
                    v___x_2663_ = crate::leanh::lean_box(0);
                    v_source_2664_ = lean_array_fset(v_source_2658_, v_i_2657_, v___x_2663_);
                    v_target_2665_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_target_2659_, v_es_2662_);
                    v___x_2666_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2667_ = lean_nat_add(v_i_2657_, v___x_2666_);
                    crate::leanh::lean_dec(v_i_2657_);
                    v_i_2657_ = v___x_2667_;
                    v_source_2658_ = v_source_2664_;
                    v_target_2659_ = v_target_2665_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(
    mut v_data_2669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2670_ = lean_array_get_size(v_data_2669_);
    v___x_2671_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2672_ = lean_nat_mul(v___x_2670_, v___x_2671_);
    v___x_2673_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2674_ = crate::leanh::lean_box(0);
    v___x_2675_ = lean_mk_array(v_nbuckets_2672_, v___x_2674_);
    v___x_2676_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v___x_2673_, v_data_2669_, v___x_2675_);
    return v___x_2676_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(
    mut v_a_2677_: *mut crate::leanh::LeanObject,
    mut v_x_2678_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2679_: u8 = 0;
    let mut v_key_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2678_) == 0 {
                    v___x_2679_ = 0;
                    return v___x_2679_;
                } else {
                    v_key_2680_ = crate::leanh::lean_ctor_get(v_x_2678_, 0);
                    v_tail_2681_ = crate::leanh::lean_ctor_get(v_x_2678_, 2);
                    v___x_2682_ = lean_nat_dec_eq(v_key_2680_, v_a_2677_);
                    if v___x_2682_ == 0 {
                        v_x_2678_ = v_tail_2681_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2682_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg___boxed(
    mut v_a_2684_: *mut crate::leanh::LeanObject,
    mut v_x_2685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2686_: u8 = 0;
    let mut v_r_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2686_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_2684_, v_x_2685_);
    crate::leanh::lean_dec(v_x_2685_);
    crate::leanh::lean_dec(v_a_2684_);
    v_r_2687_ = crate::leanh::lean_box((v_res_2686_) as usize);
    return v_r_2687_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(
    mut v_m_2688_: *mut crate::leanh::LeanObject,
    mut v_a_2689_: *mut crate::leanh::LeanObject,
    mut v_b_2690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: u64 = 0;
    let mut v___x_2695_: u64 = 0;
    let mut v___x_2696_: u64 = 0;
    let mut v_fold_2697_: u64 = 0;
    let mut v___x_2698_: u64 = 0;
    let mut v___x_2699_: u64 = 0;
    let mut v___x_2700_: u64 = 0;
    let mut v___x_2701_: usize = 0;
    let mut v___x_2702_: usize = 0;
    let mut v___x_2703_: usize = 0;
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: usize = 0;
    let mut v_bkt_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: u8 = 0;
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2710_: u8 = 0;
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: u8 = 0;
    let mut v_val_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_unused_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2691_ = crate::leanh::lean_ctor_get(v_m_2688_, 0);
                v_buckets_2692_ = crate::leanh::lean_ctor_get(v_m_2688_, 1);
                v___x_2693_ = lean_array_get_size(v_buckets_2692_);
                v___x_2694_ = lean_uint64_of_nat(v_a_2689_);
                v___x_2695_ = 32u64;
                v___x_2696_ = lean_uint64_shift_right(v___x_2694_, v___x_2695_);
                v_fold_2697_ = lean_uint64_xor(v___x_2694_, v___x_2696_);
                v___x_2698_ = 16u64;
                v___x_2699_ = lean_uint64_shift_right(v_fold_2697_, v___x_2698_);
                v___x_2700_ = lean_uint64_xor(v_fold_2697_, v___x_2699_);
                v___x_2701_ = lean_uint64_to_usize(v___x_2700_);
                v___x_2702_ = lean_usize_of_nat(v___x_2693_);
                v___x_2703_ = 1usize;
                v___x_2704_ = lean_usize_sub(v___x_2702_, v___x_2703_);
                v___x_2705_ = lean_usize_land(v___x_2701_, v___x_2704_);
                v_bkt_2706_ = lean_array_uget_borrowed(v_buckets_2692_, v___x_2705_);
                v___x_2707_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_2689_, v_bkt_2706_);
                if v___x_2707_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2692_);
                    crate::leanh::lean_inc(v_size_2691_);
                    v_isSharedCheck_2728_ = (!crate::leanh::lean_is_exclusive(v_m_2688_)) as u8;
                    if v_isSharedCheck_2728_ == 0 {
                        v_unused_2729_ = crate::leanh::lean_ctor_get(v_m_2688_, 1);
                        crate::leanh::lean_dec(v_unused_2729_);
                        v_unused_2730_ = crate::leanh::lean_ctor_get(v_m_2688_, 0);
                        crate::leanh::lean_dec(v_unused_2730_);
                        v___x_2709_ = v_m_2688_;
                        v_isShared_2710_ = v_isSharedCheck_2728_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2688_);
                        v___x_2709_ = crate::leanh::lean_box(0);
                        v_isShared_2710_ = v_isSharedCheck_2728_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2690_);
                    crate::leanh::lean_dec(v_a_2689_);
                    return v_m_2688_;
                }
            }
            1 => {
                v___x_2711_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2712_ = lean_nat_add(v_size_2691_, v___x_2711_);
                crate::leanh::lean_dec(v_size_2691_);
                crate::leanh::lean_inc(v_bkt_2706_);
                v___x_2713_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2713_, 0, v_a_2689_);
                crate::leanh::lean_ctor_set(v___x_2713_, 1, v_b_2690_);
                crate::leanh::lean_ctor_set(v___x_2713_, 2, v_bkt_2706_);
                v_buckets_x27_2714_ = lean_array_uset(v_buckets_2692_, v___x_2705_, v___x_2713_);
                v___x_2715_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2716_ = lean_nat_mul(v_size_x27_2712_, v___x_2715_);
                v___x_2717_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2718_ = lean_nat_div(v___x_2716_, v___x_2717_);
                crate::leanh::lean_dec(v___x_2716_);
                v___x_2719_ = lean_array_get_size(v_buckets_x27_2714_);
                v___x_2720_ = lean_nat_dec_le(v___x_2718_, v___x_2719_);
                crate::leanh::lean_dec(v___x_2718_);
                if v___x_2720_ == 0 {
                    v_val_2721_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_buckets_x27_2714_);
                    if v_isShared_2710_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2709_, 1, v_val_2721_);
                        crate::leanh::lean_ctor_set(v___x_2709_, 0, v_size_x27_2712_);
                        v___x_2723_ = v___x_2709_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2724_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_size_x27_2712_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_val_2721_);
                        v___x_2723_ = v_reuseFailAlloc_2724_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2710_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2709_, 1, v_buckets_x27_2714_);
                        crate::leanh::lean_ctor_set(v___x_2709_, 0, v_size_x27_2712_);
                        v___x_2726_ = v___x_2709_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_size_x27_2712_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_buckets_x27_2714_);
                        v___x_2726_ = v_reuseFailAlloc_2727_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2723_;
            }
            3 => {
                return v___x_2726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(
    mut v_numHaves_2731_: *mut crate::leanh::LeanObject,
    mut v_x_2732_: *mut crate::leanh::LeanObject,
    mut v_x_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2733_) == 0 {
                    return v_x_2732_;
                } else {
                    v_key_2734_ = crate::leanh::lean_ctor_get(v_x_2733_, 0);
                    v_tail_2735_ = crate::leanh::lean_ctor_get(v_x_2733_, 2);
                    v___x_2736_ = lean_nat_sub(v_numHaves_2731_, v_key_2734_);
                    v___x_2737_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2738_ = lean_nat_sub(v___x_2736_, v___x_2737_);
                    crate::leanh::lean_dec(v___x_2736_);
                    v___x_2739_ = crate::leanh::lean_box(0);
                    v___x_2740_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_x_2732_, v___x_2738_, v___x_2739_);
                    v_x_2732_ = v___x_2740_;
                    v_x_2733_ = v_tail_2735_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___boxed(
    mut v_numHaves_2742_: *mut crate::leanh::LeanObject,
    mut v_x_2743_: *mut crate::leanh::LeanObject,
    mut v_x_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2745_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_2742_, v_x_2743_, v_x_2744_);
    crate::leanh::lean_dec(v_x_2744_);
    crate::leanh::lean_dec(v_numHaves_2742_);
    return v_res_2745_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(
    mut v_numHaves_2746_: *mut crate::leanh::LeanObject,
    mut v_as_2747_: *mut crate::leanh::LeanObject,
    mut v_i_2748_: usize,
    mut v_stop_2749_: usize,
    mut v_b_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2751_: u8 = 0;
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: usize = 0;
    let mut v___x_2755_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2751_ = lean_usize_dec_eq(v_i_2748_, v_stop_2749_);
                if v___x_2751_ == 0 {
                    v___x_2752_ = lean_array_uget_borrowed(v_as_2747_, v_i_2748_);
                    v___x_2753_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_2746_, v_b_2750_, v___x_2752_);
                    v___x_2754_ = 1usize;
                    v___x_2755_ = lean_usize_add(v_i_2748_, v___x_2754_);
                    v_i_2748_ = v___x_2755_;
                    v_b_2750_ = v___x_2753_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2750_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2___boxed(
    mut v_numHaves_2757_: *mut crate::leanh::LeanObject,
    mut v_as_2758_: *mut crate::leanh::LeanObject,
    mut v_i_2759_: *mut crate::leanh::LeanObject,
    mut v_stop_2760_: *mut crate::leanh::LeanObject,
    mut v_b_2761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2762_: usize = 0;
    let mut v_stop_boxed_2763_: usize = 0;
    let mut v_res_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2762_ = crate::leanh::lean_unbox_usize(v_i_2759_);
    crate::leanh::lean_dec(v_i_2759_);
    v_stop_boxed_2763_ = crate::leanh::lean_unbox_usize(v_stop_2760_);
    crate::leanh::lean_dec(v_stop_2760_);
    v_res_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_2757_, v_as_2758_, v_i_boxed_2762_, v_stop_boxed_2763_, v_b_2761_);
    crate::leanh::lean_dec_ref(v_as_2758_);
    crate::leanh::lean_dec(v_numHaves_2757_);
    return v_res_2764_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(
    mut v_numHaves_2765_: *mut crate::leanh::LeanObject,
    mut v_a_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    v___x_2767_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2768_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once),
        _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1,
    );
    v___x_2769_ = l_Lean_Expr_collectLooseBVars(v_a_2766_, v___x_2767_);
    v_buckets_2770_ = crate::leanh::lean_ctor_get(v___x_2769_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2770_);
    crate::leanh::lean_dec_ref(v___x_2769_);
    v___x_2771_ = lean_array_get_size(v_buckets_2770_);
    v___x_2772_ = lean_nat_dec_lt(v___x_2767_, v___x_2771_);
    if v___x_2772_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_2770_);
        return v___x_2768_;
    } else {
        let mut v___x_2773_: u8 = 0;
        v___x_2773_ = lean_nat_dec_le(v___x_2771_, v___x_2771_);
        if v___x_2773_ == 0 {
            if v___x_2772_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_2770_);
                return v___x_2768_;
            } else {
                let mut v___x_2774_: usize = 0;
                let mut v___x_2775_: usize = 0;
                let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2774_ = 0usize;
                v___x_2775_ = lean_usize_of_nat(v___x_2771_);
                v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_2765_, v_buckets_2770_, v___x_2774_, v___x_2775_, v___x_2768_);
                crate::leanh::lean_dec_ref(v_buckets_2770_);
                return v___x_2776_;
            }
        } else {
            let mut v___x_2777_: usize = 0;
            let mut v___x_2778_: usize = 0;
            let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2777_ = 0usize;
            v___x_2778_ = lean_usize_of_nat(v___x_2771_);
            v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_2765_, v_buckets_2770_, v___x_2777_, v___x_2778_, v___x_2768_);
            crate::leanh::lean_dec_ref(v_buckets_2770_);
            return v___x_2779_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0___boxed(
    mut v_numHaves_2780_: *mut crate::leanh::LeanObject,
    mut v_a_2781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2782_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(
            v_numHaves_2780_,
            v_a_2781_,
        );
    crate::leanh::lean_dec(v_numHaves_2780_);
    return v_res_2782_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(
    mut v_k_2783_: *mut crate::leanh::LeanObject,
    mut v_t_2784_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: u8 = 0;
    let mut v___x_2790_: u8 = 0;
    let mut v___x_2792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2784_) == 0 {
                    v_k_2785_ = crate::leanh::lean_ctor_get(v_t_2784_, 1);
                    v_l_2786_ = crate::leanh::lean_ctor_get(v_t_2784_, 3);
                    v_r_2787_ = crate::leanh::lean_ctor_get(v_t_2784_, 4);
                    v___x_2788_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2783_, v_k_2785_);
                    match v___x_2788_ {
                        0 => {
                            v_t_2784_ = v_l_2786_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_2790_ = 1;
                            return v___x_2790_;
                        }
                        _ => {
                            v_t_2784_ = v_r_2787_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2792_ = 0;
                    return v___x_2792_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg___boxed(
    mut v_k_2793_: *mut crate::leanh::LeanObject,
    mut v_t_2794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2795_: u8 = 0;
    let mut v_r_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2795_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_2793_, v_t_2794_);
    crate::leanh::lean_dec(v_t_2794_);
    crate::leanh::lean_dec(v_k_2793_);
    v_r_2796_ = crate::leanh::lean_box((v_res_2795_) as usize);
    return v_r_2796_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(
    mut v_fvars_2797_: *mut crate::leanh::LeanObject,
    mut v___x_2798_: *mut crate::leanh::LeanObject,
    mut v_n_2799_: *mut crate::leanh::LeanObject,
    mut v_j_2800_: *mut crate::leanh::LeanObject,
    mut v_a_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2803_: u8 = 0;
    let mut v_one_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2802_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2803_ = lean_nat_dec_eq(v_j_2800_, v_zero_2802_);
                if v_isZero_2803_ == 1 {
                    crate::leanh::lean_dec(v_j_2800_);
                    return v_a_2801_;
                } else {
                    v_one_2804_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2805_ = lean_nat_sub(v_j_2800_, v_one_2804_);
                    v___x_2806_ = lean_nat_sub(v_n_2799_, v_j_2800_);
                    crate::leanh::lean_dec(v_j_2800_);
                    v___x_2807_ = lean_array_fget_borrowed(v_fvars_2797_, v___x_2806_);
                    v___x_2808_ = l_Lean_Expr_fvarId_x21(v___x_2807_);
                    v___x_2809_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_2808_, v___x_2798_);
                    crate::leanh::lean_dec(v___x_2808_);
                    if v___x_2809_ == 0 {
                        crate::leanh::lean_dec(v___x_2806_);
                        v_j_2800_ = v_n_2805_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2811_ = crate::leanh::lean_box(0);
                        v___x_2812_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_a_2801_, v___x_2806_, v___x_2811_);
                        v_j_2800_ = v_n_2805_;
                        v_a_2801_ = v___x_2812_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg___boxed(
    mut v_fvars_2814_: *mut crate::leanh::LeanObject,
    mut v___x_2815_: *mut crate::leanh::LeanObject,
    mut v_n_2816_: *mut crate::leanh::LeanObject,
    mut v_j_2817_: *mut crate::leanh::LeanObject,
    mut v_a_2818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2819_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_2814_, v___x_2815_, v_n_2816_, v_j_2817_, v_a_2818_);
    crate::leanh::lean_dec(v_n_2816_);
    crate::leanh::lean_dec(v___x_2815_);
    crate::leanh::lean_dec_ref(v_fvars_2814_);
    return v_res_2819_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2820_ = crate::leanh::lean_box(0);
    v___x_2821_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2822_ = lean_mk_array(v___x_2821_, v___x_2820_);
    return v___x_2822_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2823_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0);
    v___x_2824_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2825_, 0, v___x_2824_);
    crate::leanh::lean_ctor_set(v___x_2825_, 1, v___x_2823_);
    return v___x_2825_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(
    mut v_body_2828_: *mut crate::leanh::LeanObject,
    mut v___x_2829_: *mut crate::leanh::LeanObject,
    mut v_fvars_2830_: *mut crate::leanh::LeanObject,
    mut v_info_2831_: *mut crate::leanh::LeanObject,
    mut v_bodyDeps_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_haveInfo_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2855_: u8 = 0;
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2862_: u8 = 0;
    let mut v_unused_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_a_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_a_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2836_);
                crate::leanh::lean_inc_ref(v___y_2835_);
                crate::leanh::lean_inc(v___y_2834_);
                crate::leanh::lean_inc_ref(v___y_2833_);
                crate::leanh::lean_inc_ref(v_body_2828_);
                v___x_2838_ = lean_infer_type(
                    v_body_2828_,
                    v___y_2833_,
                    v___y_2834_,
                    v___y_2835_,
                    v___y_2836_,
                );
                if crate::leanh::lean_obj_tag(v___x_2838_) == 0 {
                    v_a_2839_ = crate::leanh::lean_ctor_get(v___x_2838_, 0);
                    crate::leanh::lean_inc_n(v_a_2839_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2838_, 1);
                    v___x_2840_ = l_Lean_Meta_getLevel(
                        v_a_2839_,
                        v___y_2833_,
                        v___y_2834_,
                        v___y_2835_,
                        v___y_2836_,
                    );
                    crate::leanh::lean_dec(v___y_2836_);
                    crate::leanh::lean_dec_ref(v___y_2835_);
                    crate::leanh::lean_dec(v___y_2834_);
                    crate::leanh::lean_dec_ref(v___y_2833_);
                    if crate::leanh::lean_obj_tag(v___x_2840_) == 0 {
                        v_a_2841_ = crate::leanh::lean_ctor_get(v___x_2840_, 0);
                        v_isSharedCheck_2868_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2840_)) as u8;
                        if v_isSharedCheck_2868_ == 0 {
                            v___x_2843_ = v___x_2840_;
                            v_isShared_2844_ = v_isSharedCheck_2868_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2841_);
                            crate::leanh::lean_dec(v___x_2840_);
                            v___x_2843_ = crate::leanh::lean_box(0);
                            v_isShared_2844_ = v_isSharedCheck_2868_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2839_);
                        crate::leanh::lean_dec_ref(v_bodyDeps_2832_);
                        crate::leanh::lean_dec_ref(v_info_2831_);
                        crate::leanh::lean_dec(v___x_2829_);
                        crate::leanh::lean_dec_ref(v_body_2828_);
                        v_a_2869_ = crate::leanh::lean_ctor_get(v___x_2840_, 0);
                        v_isSharedCheck_2876_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2840_)) as u8;
                        if v_isSharedCheck_2876_ == 0 {
                            v___x_2871_ = v___x_2840_;
                            v_isShared_2872_ = v_isSharedCheck_2876_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2869_);
                            crate::leanh::lean_dec(v___x_2840_);
                            v___x_2871_ = crate::leanh::lean_box(0);
                            v_isShared_2872_ = v_isSharedCheck_2876_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2836_);
                    crate::leanh::lean_dec_ref(v___y_2835_);
                    crate::leanh::lean_dec(v___y_2834_);
                    crate::leanh::lean_dec_ref(v___y_2833_);
                    crate::leanh::lean_dec_ref(v_bodyDeps_2832_);
                    crate::leanh::lean_dec_ref(v_info_2831_);
                    crate::leanh::lean_dec(v___x_2829_);
                    crate::leanh::lean_dec_ref(v_body_2828_);
                    v_a_2877_ = crate::leanh::lean_ctor_get(v___x_2838_, 0);
                    v_isSharedCheck_2884_ = (!crate::leanh::lean_is_exclusive(v___x_2838_)) as u8;
                    if v_isSharedCheck_2884_ == 0 {
                        v___x_2879_ = v___x_2838_;
                        v_isShared_2880_ = v_isSharedCheck_2884_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2877_);
                        crate::leanh::lean_dec(v___x_2838_);
                        v___x_2879_ = crate::leanh::lean_box(0);
                        v_isShared_2880_ = v_isSharedCheck_2884_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2845_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
                v___x_2846_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2;
                v___x_2847_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2847_, 0, v___x_2845_);
                crate::leanh::lean_ctor_set(v___x_2847_, 1, v___x_2829_);
                crate::leanh::lean_ctor_set(v___x_2847_, 2, v___x_2846_);
                crate::leanh::lean_inc(v_a_2839_);
                v___x_2848_ = l_Lean_collectFVars(v___x_2847_, v_a_2839_);
                v_fvarSet_2849_ = crate::leanh::lean_ctor_get(v___x_2848_, 1);
                crate::leanh::lean_inc(v_fvarSet_2849_);
                crate::leanh::lean_dec_ref(v___x_2848_);
                v___x_2850_ = lean_array_get_size(v_fvars_2830_);
                v___x_2851_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_2830_, v_fvarSet_2849_, v___x_2850_, v___x_2850_, v___x_2845_);
                crate::leanh::lean_dec(v_fvarSet_2849_);
                v_haveInfo_2852_ = crate::leanh::lean_ctor_get(v_info_2831_, 0);
                v_isSharedCheck_2862_ = (!crate::leanh::lean_is_exclusive(v_info_2831_)) as u8;
                if v_isSharedCheck_2862_ == 0 {
                    v_unused_2863_ = crate::leanh::lean_ctor_get(v_info_2831_, 5);
                    crate::leanh::lean_dec(v_unused_2863_);
                    v_unused_2864_ = crate::leanh::lean_ctor_get(v_info_2831_, 4);
                    crate::leanh::lean_dec(v_unused_2864_);
                    v_unused_2865_ = crate::leanh::lean_ctor_get(v_info_2831_, 3);
                    crate::leanh::lean_dec(v_unused_2865_);
                    v_unused_2866_ = crate::leanh::lean_ctor_get(v_info_2831_, 2);
                    crate::leanh::lean_dec(v_unused_2866_);
                    v_unused_2867_ = crate::leanh::lean_ctor_get(v_info_2831_, 1);
                    crate::leanh::lean_dec(v_unused_2867_);
                    v___x_2854_ = v_info_2831_;
                    v_isShared_2855_ = v_isSharedCheck_2862_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_haveInfo_2852_);
                    crate::leanh::lean_dec(v_info_2831_);
                    v___x_2854_ = crate::leanh::lean_box(0);
                    v_isShared_2855_ = v_isSharedCheck_2862_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2855_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2854_, 5, v_a_2841_);
                    crate::leanh::lean_ctor_set(v___x_2854_, 4, v_a_2839_);
                    crate::leanh::lean_ctor_set(v___x_2854_, 3, v_body_2828_);
                    crate::leanh::lean_ctor_set(v___x_2854_, 2, v___x_2851_);
                    crate::leanh::lean_ctor_set(v___x_2854_, 1, v_bodyDeps_2832_);
                    v___x_2857_ = v___x_2854_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2861_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_haveInfo_2852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_bodyDeps_2832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 2, v___x_2851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_body_2828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_a_2839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 5, v_a_2841_);
                    v___x_2857_ = v_reuseFailAlloc_2861_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2844_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2843_, 0, v___x_2857_);
                    v___x_2859_ = v___x_2843_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
                    v___x_2859_ = v_reuseFailAlloc_2860_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2859_;
            }
            5 => {
                if v_isShared_2872_ == 0 {
                    v___x_2874_ = v___x_2871_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
                    v___x_2874_ = v_reuseFailAlloc_2875_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2874_;
            }
            7 => {
                if v_isShared_2880_ == 0 {
                    v___x_2882_ = v___x_2879_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
                    v___x_2882_ = v_reuseFailAlloc_2883_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(
    mut v_body_2885_: *mut crate::leanh::LeanObject,
    mut v___x_2886_: *mut crate::leanh::LeanObject,
    mut v_fvars_2887_: *mut crate::leanh::LeanObject,
    mut v_info_2888_: *mut crate::leanh::LeanObject,
    mut v_bodyDeps_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
    mut v___y_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2895_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(
            v_body_2885_,
            v___x_2886_,
            v_fvars_2887_,
            v_info_2888_,
            v_bodyDeps_2889_,
            v___y_2890_,
            v___y_2891_,
            v___y_2892_,
            v___y_2893_,
        );
    crate::leanh::lean_dec_ref(v_fvars_2887_);
    return v_res_2895_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(
    mut v___y_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v_r_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2928_: u8 = 0;
    let mut v_unused_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2898_ = lean_st_ref_get(v___y_2896_);
                v_ngen_2899_ = crate::leanh::lean_ctor_get(v___x_2898_, 2);
                crate::leanh::lean_inc_ref(v_ngen_2899_);
                crate::leanh::lean_dec(v___x_2898_);
                v_namePrefix_2900_ = crate::leanh::lean_ctor_get(v_ngen_2899_, 0);
                v_idx_2901_ = crate::leanh::lean_ctor_get(v_ngen_2899_, 1);
                v_isSharedCheck_2930_ = (!crate::leanh::lean_is_exclusive(v_ngen_2899_)) as u8;
                if v_isSharedCheck_2930_ == 0 {
                    v___x_2903_ = v_ngen_2899_;
                    v_isShared_2904_ = v_isSharedCheck_2930_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_2901_);
                    crate::leanh::lean_inc(v_namePrefix_2900_);
                    crate::leanh::lean_dec(v_ngen_2899_);
                    v___x_2903_ = crate::leanh::lean_box(0);
                    v_isShared_2904_ = v_isSharedCheck_2930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2905_ = lean_st_ref_take(v___y_2896_);
                v_env_2906_ = crate::leanh::lean_ctor_get(v___x_2905_, 0);
                v_nextMacroScope_2907_ = crate::leanh::lean_ctor_get(v___x_2905_, 1);
                v_auxDeclNGen_2908_ = crate::leanh::lean_ctor_get(v___x_2905_, 3);
                v_traceState_2909_ = crate::leanh::lean_ctor_get(v___x_2905_, 4);
                v_cache_2910_ = crate::leanh::lean_ctor_get(v___x_2905_, 5);
                v_messages_2911_ = crate::leanh::lean_ctor_get(v___x_2905_, 6);
                v_infoState_2912_ = crate::leanh::lean_ctor_get(v___x_2905_, 7);
                v_snapshotTasks_2913_ = crate::leanh::lean_ctor_get(v___x_2905_, 8);
                v_isSharedCheck_2928_ = (!crate::leanh::lean_is_exclusive(v___x_2905_)) as u8;
                if v_isSharedCheck_2928_ == 0 {
                    v_unused_2929_ = crate::leanh::lean_ctor_get(v___x_2905_, 2);
                    crate::leanh::lean_dec(v_unused_2929_);
                    v___x_2915_ = v___x_2905_;
                    v_isShared_2916_ = v_isSharedCheck_2928_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2913_);
                    crate::leanh::lean_inc(v_infoState_2912_);
                    crate::leanh::lean_inc(v_messages_2911_);
                    crate::leanh::lean_inc(v_cache_2910_);
                    crate::leanh::lean_inc(v_traceState_2909_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2908_);
                    crate::leanh::lean_inc(v_nextMacroScope_2907_);
                    crate::leanh::lean_inc(v_env_2906_);
                    crate::leanh::lean_dec(v___x_2905_);
                    v___x_2915_ = crate::leanh::lean_box(0);
                    v_isShared_2916_ = v_isSharedCheck_2928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_2901_);
                crate::leanh::lean_inc(v_namePrefix_2900_);
                v_r_2917_ = l_Lean_Name_num___override(v_namePrefix_2900_, v_idx_2901_);
                v___x_2918_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2919_ = lean_nat_add(v_idx_2901_, v___x_2918_);
                crate::leanh::lean_dec(v_idx_2901_);
                if v_isShared_2904_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2903_, 1, v___x_2919_);
                    v___x_2921_ = v___x_2903_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2927_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_namePrefix_2900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2927_, 1, v___x_2919_);
                    v___x_2921_ = v_reuseFailAlloc_2927_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2916_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2915_, 2, v___x_2921_);
                    v___x_2923_ = v___x_2915_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2926_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_env_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_nextMacroScope_2907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2926_, 2, v___x_2921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2926_, 3, v_auxDeclNGen_2908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2926_, 4, v_traceState_2909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2926_, 5, v_cache_2910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2926_, 6, v_messages_2911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2926_, 7, v_infoState_2912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2926_, 8, v_snapshotTasks_2913_);
                    v___x_2923_ = v_reuseFailAlloc_2926_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2924_ = lean_st_ref_set(v___y_2896_, v___x_2923_);
                v___x_2925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2925_, 0, v_r_2917_);
                return v___x_2925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg___boxed(
    mut v___y_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2933_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_2931_);
    crate::leanh::lean_dec(v___y_2931_);
    return v_res_2933_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2939_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_2937_);
                v_a_2940_ = crate::leanh::lean_ctor_get(v___x_2939_, 0);
                v_isSharedCheck_2947_ = (!crate::leanh::lean_is_exclusive(v___x_2939_)) as u8;
                if v_isSharedCheck_2947_ == 0 {
                    v___x_2942_ = v___x_2939_;
                    v_isShared_2943_ = v_isSharedCheck_2947_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2940_);
                    crate::leanh::lean_dec(v___x_2939_);
                    v___x_2942_ = crate::leanh::lean_box(0);
                    v_isShared_2943_ = v_isSharedCheck_2947_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2943_ == 0 {
                    v___x_2945_ = v___x_2942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2946_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
                    v___x_2945_ = v_reuseFailAlloc_2946_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(
    mut v___y_2948_: *mut crate::leanh::LeanObject,
    mut v___y_2949_: *mut crate::leanh::LeanObject,
    mut v___y_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
    crate::leanh::lean_dec(v___y_2951_);
    crate::leanh::lean_dec_ref(v___y_2950_);
    crate::leanh::lean_dec(v___y_2949_);
    crate::leanh::lean_dec_ref(v___y_2948_);
    return v_res_2953_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(
    mut v_e_2954_: *mut crate::leanh::LeanObject,
    mut v_numHaves_2955_: *mut crate::leanh::LeanObject,
    mut v_info_2956_: *mut crate::leanh::LeanObject,
    mut v_lctx_2957_: *mut crate::leanh::LeanObject,
    mut v_fvars_2958_: *mut crate::leanh::LeanObject,
    mut v_a_2959_: *mut crate::leanh::LeanObject,
    mut v_a_2960_: *mut crate::leanh::LeanObject,
    mut v_a_2961_: *mut crate::leanh::LeanObject,
    mut v_a_2962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyDeps_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2974_: u8 = 0;
    let mut v_declName_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_haveInfo_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyDeps_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyTypeDeps_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyType_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_level_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2993_: u8 = 0;
    let mut v_typeBackDeps_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueBackDeps_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3011_: u8 = 0;
    let mut v_a_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3019_: u8 = 0;
    let mut v_a_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2964_ = crate::leanh::lean_box(1);
                if crate::leanh::lean_obj_tag(v_e_2954_) == 8 {
                    v_nondep_2974_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_2954_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    if v_nondep_2974_ == 1 {
                        v_declName_2975_ = crate::leanh::lean_ctor_get(v_e_2954_, 0);
                        crate::leanh::lean_inc(v_declName_2975_);
                        v_type_2976_ = crate::leanh::lean_ctor_get(v_e_2954_, 1);
                        crate::leanh::lean_inc_ref(v_type_2976_);
                        v_value_2977_ = crate::leanh::lean_ctor_get(v_e_2954_, 2);
                        crate::leanh::lean_inc_ref(v_value_2977_);
                        v_body_2978_ = crate::leanh::lean_ctor_get(v_e_2954_, 3);
                        crate::leanh::lean_inc_ref(v_body_2978_);
                        crate::leanh::lean_dec_ref_known(v_e_2954_, 4);
                        v_t_2979_ = lean_expr_instantiate_rev(v_type_2976_, v_fvars_2958_);
                        crate::leanh::lean_inc_ref(v_t_2979_);
                        v___x_2980_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_2980_, 0, v_t_2979_);
                        crate::leanh::lean_inc_ref(v_lctx_2957_);
                        v___x_2981_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_2957_, v___x_2980_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
                        if crate::leanh::lean_obj_tag(v___x_2981_) == 0 {
                            v_a_2982_ = crate::leanh::lean_ctor_get(v___x_2981_, 0);
                            crate::leanh::lean_inc(v_a_2982_);
                            crate::leanh::lean_dec_ref_known(v___x_2981_, 1);
                            v___x_2983_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
                            if crate::leanh::lean_obj_tag(v___x_2983_) == 0 {
                                v_a_2984_ = crate::leanh::lean_ctor_get(v___x_2983_, 0);
                                crate::leanh::lean_inc(v_a_2984_);
                                crate::leanh::lean_dec_ref_known(v___x_2983_, 1);
                                v_haveInfo_2985_ = crate::leanh::lean_ctor_get(v_info_2956_, 0);
                                v_bodyDeps_2986_ = crate::leanh::lean_ctor_get(v_info_2956_, 1);
                                v_bodyTypeDeps_2987_ = crate::leanh::lean_ctor_get(v_info_2956_, 2);
                                v_body_2988_ = crate::leanh::lean_ctor_get(v_info_2956_, 3);
                                v_bodyType_2989_ = crate::leanh::lean_ctor_get(v_info_2956_, 4);
                                v_level_2990_ = crate::leanh::lean_ctor_get(v_info_2956_, 5);
                                v_isSharedCheck_3011_ =
                                    (!crate::leanh::lean_is_exclusive(v_info_2956_)) as u8;
                                if v_isSharedCheck_3011_ == 0 {
                                    v___x_2992_ = v_info_2956_;
                                    v_isShared_2993_ = v_isSharedCheck_3011_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_level_2990_);
                                    crate::leanh::lean_inc(v_bodyType_2989_);
                                    crate::leanh::lean_inc(v_body_2988_);
                                    crate::leanh::lean_inc(v_bodyTypeDeps_2987_);
                                    crate::leanh::lean_inc(v_bodyDeps_2986_);
                                    crate::leanh::lean_inc(v_haveInfo_2985_);
                                    crate::leanh::lean_dec(v_info_2956_);
                                    v___x_2992_ = crate::leanh::lean_box(0);
                                    v_isShared_2993_ = v_isSharedCheck_3011_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2982_);
                                crate::leanh::lean_dec_ref(v_t_2979_);
                                crate::leanh::lean_dec_ref(v_body_2978_);
                                crate::leanh::lean_dec_ref(v_value_2977_);
                                crate::leanh::lean_dec_ref(v_type_2976_);
                                crate::leanh::lean_dec(v_declName_2975_);
                                crate::leanh::lean_dec_ref(v_fvars_2958_);
                                crate::leanh::lean_dec_ref(v_lctx_2957_);
                                crate::leanh::lean_dec_ref(v_info_2956_);
                                crate::leanh::lean_dec(v_numHaves_2955_);
                                v_a_3012_ = crate::leanh::lean_ctor_get(v___x_2983_, 0);
                                v_isSharedCheck_3019_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2983_)) as u8;
                                if v_isSharedCheck_3019_ == 0 {
                                    v___x_3014_ = v___x_2983_;
                                    v_isShared_3015_ = v_isSharedCheck_3019_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3012_);
                                    crate::leanh::lean_dec(v___x_2983_);
                                    v___x_3014_ = crate::leanh::lean_box(0);
                                    v_isShared_3015_ = v_isSharedCheck_3019_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_t_2979_);
                            crate::leanh::lean_dec_ref(v_body_2978_);
                            crate::leanh::lean_dec_ref(v_value_2977_);
                            crate::leanh::lean_dec_ref(v_type_2976_);
                            crate::leanh::lean_dec(v_declName_2975_);
                            crate::leanh::lean_dec_ref(v_fvars_2958_);
                            crate::leanh::lean_dec_ref(v_lctx_2957_);
                            crate::leanh::lean_dec_ref(v_info_2956_);
                            crate::leanh::lean_dec(v_numHaves_2955_);
                            v_a_3020_ = crate::leanh::lean_ctor_get(v___x_2981_, 0);
                            v_isSharedCheck_3027_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2981_)) as u8;
                            if v_isSharedCheck_3027_ == 0 {
                                v___x_3022_ = v___x_2981_;
                                v_isShared_3023_ = v_isSharedCheck_3027_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3020_);
                                crate::leanh::lean_dec(v___x_2981_);
                                v___x_3022_ = crate::leanh::lean_box(0);
                                v_isShared_3023_ = v_isSharedCheck_3027_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___y_2966_ = v_a_2959_;
                        v___y_2967_ = v_a_2960_;
                        v___y_2968_ = v_a_2961_;
                        v___y_2969_ = v_a_2962_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_2966_ = v_a_2959_;
                    v___y_2967_ = v_a_2960_;
                    v___y_2968_ = v_a_2961_;
                    v___y_2969_ = v_a_2962_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_e_2954_);
                v_bodyDeps_2970_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_2955_, v_e_2954_);
                crate::leanh::lean_dec(v_numHaves_2955_);
                v_body_2971_ = lean_expr_instantiate_rev(v_e_2954_, v_fvars_2958_);
                crate::leanh::lean_dec_ref(v_e_2954_);
                v___f_2972_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_2972_, 0, v_body_2971_);
                crate::leanh::lean_closure_set(v___f_2972_, 1, v___x_2964_);
                crate::leanh::lean_closure_set(v___f_2972_, 2, v_fvars_2958_);
                crate::leanh::lean_closure_set(v___f_2972_, 3, v_info_2956_);
                crate::leanh::lean_closure_set(v___f_2972_, 4, v_bodyDeps_2970_);
                v___x_2973_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_2957_, v___f_2972_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
                return v___x_2973_;
            }
            2 => {
                v_typeBackDeps_2994_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_2955_, v_type_2976_);
                crate::leanh::lean_inc_ref(v_value_2977_);
                v_valueBackDeps_2995_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_2955_, v_value_2977_);
                v_v_2996_ = lean_expr_instantiate_rev(v_value_2977_, v_fvars_2958_);
                crate::leanh::lean_dec_ref(v_value_2977_);
                v___x_2997_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2998_ = 0;
                crate::leanh::lean_inc(v_a_2984_);
                v___x_2999_ = crate::leanh::lean_alloc_ctor(1, 5, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2999_, 0, v___x_2997_);
                crate::leanh::lean_ctor_set(v___x_2999_, 1, v_a_2984_);
                crate::leanh::lean_ctor_set(v___x_2999_, 2, v_declName_2975_);
                crate::leanh::lean_ctor_set(v___x_2999_, 3, v_t_2979_);
                crate::leanh::lean_ctor_set(v___x_2999_, 4, v_v_2996_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2999_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_nondep_2974_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2999_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_2998_,
                );
                crate::leanh::lean_inc_ref(v___x_2999_);
                v___x_3000_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3000_, 0, v_typeBackDeps_2994_);
                crate::leanh::lean_ctor_set(v___x_3000_, 1, v_valueBackDeps_2995_);
                crate::leanh::lean_ctor_set(v___x_3000_, 2, v___x_2999_);
                crate::leanh::lean_ctor_set(v___x_3000_, 3, v_a_2982_);
                v___x_3001_ = lean_array_push(v_haveInfo_2985_, v___x_3000_);
                if v_isShared_2993_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2992_, 0, v___x_3001_);
                    v___x_3003_ = v___x_2992_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3010_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_bodyDeps_2986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 2, v_bodyTypeDeps_2987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 3, v_body_2988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 4, v_bodyType_2989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 5, v_level_2990_);
                    v___x_3003_ = v_reuseFailAlloc_3010_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3004_ = l_Lean_LocalContext_addDecl(v_lctx_2957_, v___x_2999_);
                v___x_3005_ = l_Lean_mkFVar(v_a_2984_);
                v___x_3006_ = lean_array_push(v_fvars_2958_, v___x_3005_);
                v___x_3007_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3008_ = lean_nat_add(v_numHaves_2955_, v___x_3007_);
                crate::leanh::lean_dec(v_numHaves_2955_);
                v_e_2954_ = v_body_2978_;
                v_numHaves_2955_ = v___x_3008_;
                v_info_2956_ = v___x_3003_;
                v_lctx_2957_ = v___x_3004_;
                v_fvars_2958_ = v___x_3006_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_3015_ == 0 {
                    v___x_3017_ = v___x_3014_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
                    v___x_3017_ = v_reuseFailAlloc_3018_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3017_;
            }
            6 => {
                if v_isShared_3023_ == 0 {
                    v___x_3025_ = v___x_3022_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3026_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
                    v___x_3025_ = v_reuseFailAlloc_3026_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(
    mut v_e_3028_: *mut crate::leanh::LeanObject,
    mut v_numHaves_3029_: *mut crate::leanh::LeanObject,
    mut v_info_3030_: *mut crate::leanh::LeanObject,
    mut v_lctx_3031_: *mut crate::leanh::LeanObject,
    mut v_fvars_3032_: *mut crate::leanh::LeanObject,
    mut v_a_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
    mut v_a_3035_: *mut crate::leanh::LeanObject,
    mut v_a_3036_: *mut crate::leanh::LeanObject,
    mut v_a_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3038_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(
        v_e_3028_,
        v_numHaves_3029_,
        v_info_3030_,
        v_lctx_3031_,
        v_fvars_3032_,
        v_a_3033_,
        v_a_3034_,
        v_a_3035_,
        v_a_3036_,
    );
    crate::leanh::lean_dec(v_a_3036_);
    crate::leanh::lean_dec_ref(v_a_3035_);
    crate::leanh::lean_dec(v_a_3034_);
    crate::leanh::lean_dec_ref(v_a_3033_);
    return v_res_3038_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(
    mut v_00_u03b2_3039_: *mut crate::leanh::LeanObject,
    mut v_m_3040_: *mut crate::leanh::LeanObject,
    mut v_a_3041_: *mut crate::leanh::LeanObject,
    mut v_b_3042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_3040_, v_a_3041_, v_b_3042_);
    return v___x_3043_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(
    mut v_00_u03b2_3044_: *mut crate::leanh::LeanObject,
    mut v_k_3045_: *mut crate::leanh::LeanObject,
    mut v_t_3046_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3047_: u8 = 0;
    v___x_3047_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_3045_, v_t_3046_);
    return v___x_3047_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(
    mut v_00_u03b2_3048_: *mut crate::leanh::LeanObject,
    mut v_k_3049_: *mut crate::leanh::LeanObject,
    mut v_t_3050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3051_: u8 = 0;
    let mut v_r_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3051_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_3048_, v_k_3049_, v_t_3050_);
    crate::leanh::lean_dec(v_t_3050_);
    crate::leanh::lean_dec(v_k_3049_);
    v_r_3052_ = crate::leanh::lean_box((v_res_3051_) as usize);
    return v_r_3052_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(
    mut v_fvars_3053_: *mut crate::leanh::LeanObject,
    mut v___x_3054_: *mut crate::leanh::LeanObject,
    mut v_n_3055_: *mut crate::leanh::LeanObject,
    mut v_j_3056_: *mut crate::leanh::LeanObject,
    mut v_a_3057_: *mut crate::leanh::LeanObject,
    mut v_a_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3059_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_3053_, v___x_3054_, v_n_3055_, v_j_3056_, v_a_3058_);
    return v___x_3059_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(
    mut v_fvars_3060_: *mut crate::leanh::LeanObject,
    mut v___x_3061_: *mut crate::leanh::LeanObject,
    mut v_n_3062_: *mut crate::leanh::LeanObject,
    mut v_j_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
    mut v_a_3065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3066_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_3060_, v___x_3061_, v_n_3062_, v_j_3063_, v_a_3064_, v_a_3065_);
    crate::leanh::lean_dec(v_n_3062_);
    crate::leanh::lean_dec(v___x_3061_);
    crate::leanh::lean_dec_ref(v_fvars_3060_);
    return v_res_3066_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(
    mut v___y_3067_: *mut crate::leanh::LeanObject,
    mut v___y_3068_: *mut crate::leanh::LeanObject,
    mut v___y_3069_: *mut crate::leanh::LeanObject,
    mut v___y_3070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3072_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_3070_);
    return v___x_3072_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(
    mut v___y_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3078_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
    crate::leanh::lean_dec(v___y_3076_);
    crate::leanh::lean_dec_ref(v___y_3075_);
    crate::leanh::lean_dec(v___y_3074_);
    crate::leanh::lean_dec_ref(v___y_3073_);
    return v_res_3078_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(
    mut v_00_u03b2_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_x_3081_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3082_: u8 = 0;
    v___x_3082_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_3080_, v_x_3081_);
    return v___x_3082_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(
    mut v_00_u03b2_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_x_3085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3086_: u8 = 0;
    let mut v_r_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3086_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_3083_, v_a_3084_, v_x_3085_);
    crate::leanh::lean_dec(v_x_3085_);
    crate::leanh::lean_dec(v_a_3084_);
    v_r_3087_ = crate::leanh::lean_box((v_res_3086_) as usize);
    return v_r_3087_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(
    mut v_00_u03b2_3088_: *mut crate::leanh::LeanObject,
    mut v_data_3089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3090_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_data_3089_);
    return v___x_3090_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3091_: *mut crate::leanh::LeanObject,
    mut v_i_3092_: *mut crate::leanh::LeanObject,
    mut v_source_3093_: *mut crate::leanh::LeanObject,
    mut v_target_3094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3095_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v_i_3092_, v_source_3093_, v_target_3094_);
    return v___x_3095_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(
    mut v_00_u03b2_3096_: *mut crate::leanh::LeanObject,
    mut v_x_3097_: *mut crate::leanh::LeanObject,
    mut v_x_3098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3099_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_x_3097_, v_x_3098_);
    return v___x_3099_;
}
pub unsafe fn l_Lean_Meta_getHaveTelescopeInfo(
    mut v_e_3100_: *mut crate::leanh::LeanObject,
    mut v_a_3101_: *mut crate::leanh::LeanObject,
    mut v_a_3102_: *mut crate::leanh::LeanObject,
    mut v_a_3103_: *mut crate::leanh::LeanObject,
    mut v_a_3104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_3106_ = crate::leanh::lean_ctor_get(v_a_3101_, 2);
    v___x_3107_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3108_ = l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0;
    v___x_3109_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once
        ),
        _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5,
    );
    crate::leanh::lean_inc_ref(v_lctx_3106_);
    v___x_3110_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(
        v_e_3100_,
        v___x_3107_,
        v___x_3109_,
        v_lctx_3106_,
        v___x_3108_,
        v_a_3101_,
        v_a_3102_,
        v_a_3103_,
        v_a_3104_,
    );
    return v___x_3110_;
}
pub unsafe fn l_Lean_Meta_getHaveTelescopeInfo___boxed(
    mut v_e_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_a_3114_: *mut crate::leanh::LeanObject,
    mut v_a_3115_: *mut crate::leanh::LeanObject,
    mut v_a_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3117_ =
        l_Lean_Meta_getHaveTelescopeInfo(v_e_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_);
    crate::leanh::lean_dec(v_a_3115_);
    crate::leanh::lean_dec_ref(v_a_3114_);
    crate::leanh::lean_dec(v_a_3113_);
    crate::leanh::lean_dec_ref(v_a_3112_);
    return v_res_3117_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(
    mut v_x_3118_: *mut crate::leanh::LeanObject,
    mut v_x_3119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3119_) == 0 {
                    return v_x_3118_;
                } else {
                    v_key_3120_ = crate::leanh::lean_ctor_get(v_x_3119_, 0);
                    v_tail_3121_ = crate::leanh::lean_ctor_get(v_x_3119_, 2);
                    v___x_3122_ = 1;
                    v___x_3123_ = crate::leanh::lean_box((v___x_3122_) as usize);
                    v___x_3124_ = lean_array_set(v_x_3118_, v_key_3120_, v___x_3123_);
                    v_x_3118_ = v___x_3124_;
                    v_x_3119_ = v_tail_3121_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(
    mut v_x_3126_: *mut crate::leanh::LeanObject,
    mut v_x_3127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3128_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_3126_, v_x_3127_);
    crate::leanh::lean_dec(v_x_3127_);
    return v_res_3128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(
    mut v_as_3129_: *mut crate::leanh::LeanObject,
    mut v_i_3130_: usize,
    mut v_stop_3131_: usize,
    mut v_b_3132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3133_: u8 = 0;
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: usize = 0;
    let mut v___x_3137_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3133_ = lean_usize_dec_eq(v_i_3130_, v_stop_3131_);
                if v___x_3133_ == 0 {
                    v___x_3134_ = lean_array_uget_borrowed(v_as_3129_, v_i_3130_);
                    v___x_3135_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_3132_, v___x_3134_);
                    v___x_3136_ = 1usize;
                    v___x_3137_ = lean_usize_add(v_i_3130_, v___x_3136_);
                    v_i_3130_ = v___x_3137_;
                    v_b_3132_ = v___x_3135_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3132_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(
    mut v_as_3139_: *mut crate::leanh::LeanObject,
    mut v_i_3140_: *mut crate::leanh::LeanObject,
    mut v_stop_3141_: *mut crate::leanh::LeanObject,
    mut v_b_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3143_: usize = 0;
    let mut v_stop_boxed_3144_: usize = 0;
    let mut v_res_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3143_ = crate::leanh::lean_unbox_usize(v_i_3140_);
    crate::leanh::lean_dec(v_i_3140_);
    v_stop_boxed_3144_ = crate::leanh::lean_unbox_usize(v_stop_3141_);
    crate::leanh::lean_dec(v_stop_3141_);
    v_res_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_3139_, v_i_boxed_3143_, v_stop_boxed_3144_, v_b_3142_);
    crate::leanh::lean_dec_ref(v_as_3139_);
    return v_res_3145_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(
    mut v_arr_3146_: *mut crate::leanh::LeanObject,
    mut v_s_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: u8 = 0;
    v_buckets_3148_ = crate::leanh::lean_ctor_get(v_s_3147_, 1);
    v___x_3149_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3150_ = lean_array_get_size(v_buckets_3148_);
    v___x_3151_ = lean_nat_dec_lt(v___x_3149_, v___x_3150_);
    if v___x_3151_ == 0 {
        return v_arr_3146_;
    } else {
        let mut v___x_3152_: u8 = 0;
        v___x_3152_ = lean_nat_dec_le(v___x_3150_, v___x_3150_);
        if v___x_3152_ == 0 {
            if v___x_3151_ == 0 {
                return v_arr_3146_;
            } else {
                let mut v___x_3153_: usize = 0;
                let mut v___x_3154_: usize = 0;
                let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3153_ = 0usize;
                v___x_3154_ = lean_usize_of_nat(v___x_3150_);
                v___x_3155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_3148_, v___x_3153_, v___x_3154_, v_arr_3146_);
                return v___x_3155_;
            }
        } else {
            let mut v___x_3156_: usize = 0;
            let mut v___x_3157_: usize = 0;
            let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3156_ = 0usize;
            v___x_3157_ = lean_usize_of_nat(v___x_3150_);
            v___x_3158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_3148_, v___x_3156_, v___x_3157_, v_arr_3146_);
            return v___x_3158_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(
    mut v_arr_3159_: *mut crate::leanh::LeanObject,
    mut v_s_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3161_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_3159_, v_s_3160_);
    crate::leanh::lean_dec_ref(v_s_3160_);
    return v_res_3161_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(
    mut v_upperBound_3162_: *mut crate::leanh::LeanObject,
    mut v_numHaves_3163_: *mut crate::leanh::LeanObject,
    mut v___x_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
    mut v_b_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeBackDeps_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueBackDeps_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3173_ = lean_nat_dec_lt(v_a_3165_, v_upperBound_3162_);
                if v___x_3173_ == 0 {
                    crate::leanh::lean_dec(v_a_3165_);
                    v___x_3174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3174_, 0, v_b_3166_);
                    return v___x_3174_;
                } else {
                    v___x_3175_ = 0;
                    v___x_3176_ = lean_nat_sub(v_numHaves_3163_, v_a_3165_);
                    v___x_3177_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3178_ = lean_nat_sub(v___x_3176_, v___x_3177_);
                    crate::leanh::lean_dec(v___x_3176_);
                    v___x_3179_ = crate::leanh::lean_box((v___x_3175_) as usize);
                    v___x_3180_ = lean_array_get(v___x_3179_, v_b_3166_, v___x_3178_);
                    crate::leanh::lean_dec(v___x_3179_);
                    v___x_3181_ = (crate::leanh::lean_unbox(v___x_3180_) as u8);
                    crate::leanh::lean_dec(v___x_3180_);
                    if v___x_3181_ == 0 {
                        crate::leanh::lean_dec(v___x_3178_);
                        v_a_3169_ = v_b_3166_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3182_ = l_Lean_Meta_instInhabitedHaveInfo_default;
                        v___x_3183_ =
                            lean_array_get_borrowed(v___x_3182_, v___x_3164_, v___x_3178_);
                        crate::leanh::lean_dec(v___x_3178_);
                        v_typeBackDeps_3184_ = crate::leanh::lean_ctor_get(v___x_3183_, 0);
                        v_valueBackDeps_3185_ = crate::leanh::lean_ctor_get(v___x_3183_, 1);
                        v___x_3186_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_3166_, v_typeBackDeps_3184_);
                        v___x_3187_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_3186_, v_valueBackDeps_3185_);
                        v_a_3169_ = v___x_3187_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3170_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3171_ = lean_nat_add(v_a_3165_, v___x_3170_);
                crate::leanh::lean_dec(v_a_3165_);
                v_a_3165_ = v___x_3171_;
                v_b_3166_ = v_a_3169_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(
    mut v_upperBound_3188_: *mut crate::leanh::LeanObject,
    mut v_numHaves_3189_: *mut crate::leanh::LeanObject,
    mut v___x_3190_: *mut crate::leanh::LeanObject,
    mut v_a_3191_: *mut crate::leanh::LeanObject,
    mut v_b_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3194_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_3188_, v_numHaves_3189_, v___x_3190_, v_a_3191_, v_b_3192_);
    crate::leanh::lean_dec_ref(v___x_3190_);
    crate::leanh::lean_dec(v_numHaves_3189_);
    crate::leanh::lean_dec(v_upperBound_3188_);
    return v_res_3194_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(
    mut v_info_3195_: *mut crate::leanh::LeanObject,
    mut v_init_3196_: *mut crate::leanh::LeanObject,
    mut v_a_3197_: *mut crate::leanh::LeanObject,
    mut v_a_3198_: *mut crate::leanh::LeanObject,
    mut v_a_3199_: *mut crate::leanh::LeanObject,
    mut v_a_3200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_haveInfo_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numHaves_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_haveInfo_3202_ = crate::leanh::lean_ctor_get(v_info_3195_, 0);
    v_numHaves_3203_ = lean_array_get_size(v_haveInfo_3202_);
    v___x_3204_ = 0;
    v___x_3205_ = crate::leanh::lean_box((v___x_3204_) as usize);
    v_used_3206_ = lean_mk_array(v_numHaves_3203_, v___x_3205_);
    v___x_3207_ = crate::leanh::lean_unsigned_to_nat(0);
    v_used_3208_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_3206_, v_init_3196_);
    v___x_3209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_3203_, v_numHaves_3203_, v_haveInfo_3202_, v___x_3207_, v_used_3208_);
    return v___x_3209_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(
    mut v_info_3210_: *mut crate::leanh::LeanObject,
    mut v_init_3211_: *mut crate::leanh::LeanObject,
    mut v_a_3212_: *mut crate::leanh::LeanObject,
    mut v_a_3213_: *mut crate::leanh::LeanObject,
    mut v_a_3214_: *mut crate::leanh::LeanObject,
    mut v_a_3215_: *mut crate::leanh::LeanObject,
    mut v_a_3216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3217_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(
            v_info_3210_,
            v_init_3211_,
            v_a_3212_,
            v_a_3213_,
            v_a_3214_,
            v_a_3215_,
        );
    crate::leanh::lean_dec(v_a_3215_);
    crate::leanh::lean_dec_ref(v_a_3214_);
    crate::leanh::lean_dec(v_a_3213_);
    crate::leanh::lean_dec_ref(v_a_3212_);
    crate::leanh::lean_dec_ref(v_init_3211_);
    crate::leanh::lean_dec_ref(v_info_3210_);
    return v_res_3217_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(
    mut v_upperBound_3218_: *mut crate::leanh::LeanObject,
    mut v_numHaves_3219_: *mut crate::leanh::LeanObject,
    mut v___x_3220_: *mut crate::leanh::LeanObject,
    mut v_inst_3221_: *mut crate::leanh::LeanObject,
    mut v_R_3222_: *mut crate::leanh::LeanObject,
    mut v_a_3223_: *mut crate::leanh::LeanObject,
    mut v_b_3224_: *mut crate::leanh::LeanObject,
    mut v_c_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3231_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_3218_, v_numHaves_3219_, v___x_3220_, v_a_3223_, v_b_3224_);
    return v___x_3231_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(
    mut v_upperBound_3232_: *mut crate::leanh::LeanObject,
    mut v_numHaves_3233_: *mut crate::leanh::LeanObject,
    mut v___x_3234_: *mut crate::leanh::LeanObject,
    mut v_inst_3235_: *mut crate::leanh::LeanObject,
    mut v_R_3236_: *mut crate::leanh::LeanObject,
    mut v_a_3237_: *mut crate::leanh::LeanObject,
    mut v_b_3238_: *mut crate::leanh::LeanObject,
    mut v_c_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3245_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_3232_, v_numHaves_3233_, v___x_3234_, v_inst_3235_, v_R_3236_, v_a_3237_, v_b_3238_, v_c_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
    crate::leanh::lean_dec(v___y_3243_);
    crate::leanh::lean_dec_ref(v___y_3242_);
    crate::leanh::lean_dec(v___y_3241_);
    crate::leanh::lean_dec_ref(v___y_3240_);
    crate::leanh::lean_dec_ref(v___x_3234_);
    crate::leanh::lean_dec(v_numHaves_3233_);
    crate::leanh::lean_dec(v_upperBound_3232_);
    return v_res_3245_;
}
pub unsafe fn l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(
    mut v_info_3248_: *mut crate::leanh::LeanObject,
    mut v_keepUnused_3249_: u8,
    mut v_a_3250_: *mut crate::leanh::LeanObject,
    mut v_a_3251_: *mut crate::leanh::LeanObject,
    mut v_a_3252_: *mut crate::leanh::LeanObject,
    mut v_a_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bodyDeps_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyTypeDeps_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3263_: u8 = 0;
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut v_a_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3276_: u8 = 0;
    let mut v_a_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3280_: u8 = 0;
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_a_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_bodyDeps_3255_ = crate::leanh::lean_ctor_get(v_info_3248_, 1);
                v_bodyTypeDeps_3256_ = crate::leanh::lean_ctor_get(v_info_3248_, 2);
                v___x_3257_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_3248_, v_bodyTypeDeps_3256_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
                if crate::leanh::lean_obj_tag(v___x_3257_) == 0 {
                    if v_keepUnused_3249_ == 0 {
                        v_a_3258_ = crate::leanh::lean_ctor_get(v___x_3257_, 0);
                        crate::leanh::lean_inc(v_a_3258_);
                        crate::leanh::lean_dec_ref_known(v___x_3257_, 1);
                        v___x_3259_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_3248_, v_bodyDeps_3255_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
                        if crate::leanh::lean_obj_tag(v___x_3259_) == 0 {
                            v_a_3260_ = crate::leanh::lean_ctor_get(v___x_3259_, 0);
                            v_isSharedCheck_3268_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3259_)) as u8;
                            if v_isSharedCheck_3268_ == 0 {
                                v___x_3262_ = v___x_3259_;
                                v_isShared_3263_ = v_isSharedCheck_3268_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3260_);
                                crate::leanh::lean_dec(v___x_3259_);
                                v___x_3262_ = crate::leanh::lean_box(0);
                                v_isShared_3263_ = v_isSharedCheck_3268_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3258_);
                            v_a_3269_ = crate::leanh::lean_ctor_get(v___x_3259_, 0);
                            v_isSharedCheck_3276_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3259_)) as u8;
                            if v_isSharedCheck_3276_ == 0 {
                                v___x_3271_ = v___x_3259_;
                                v_isShared_3272_ = v_isSharedCheck_3276_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3269_);
                                crate::leanh::lean_dec(v___x_3259_);
                                v___x_3271_ = crate::leanh::lean_box(0);
                                v_isShared_3272_ = v_isSharedCheck_3276_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_3277_ = crate::leanh::lean_ctor_get(v___x_3257_, 0);
                        v_isSharedCheck_3286_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3257_)) as u8;
                        if v_isSharedCheck_3286_ == 0 {
                            v___x_3279_ = v___x_3257_;
                            v_isShared_3280_ = v_isSharedCheck_3286_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3277_);
                            crate::leanh::lean_dec(v___x_3257_);
                            v___x_3279_ = crate::leanh::lean_box(0);
                            v_isShared_3280_ = v_isSharedCheck_3286_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_3287_ = crate::leanh::lean_ctor_get(v___x_3257_, 0);
                    v_isSharedCheck_3294_ = (!crate::leanh::lean_is_exclusive(v___x_3257_)) as u8;
                    if v_isSharedCheck_3294_ == 0 {
                        v___x_3289_ = v___x_3257_;
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3287_);
                        crate::leanh::lean_dec(v___x_3257_);
                        v___x_3289_ = crate::leanh::lean_box(0);
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3264_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3264_, 0, v_a_3258_);
                crate::leanh::lean_ctor_set(v___x_3264_, 1, v_a_3260_);
                if v_isShared_3263_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3262_, 0, v___x_3264_);
                    v___x_3266_ = v___x_3262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
                    v___x_3266_ = v_reuseFailAlloc_3267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3266_;
            }
            3 => {
                if v_isShared_3272_ == 0 {
                    v___x_3274_ = v___x_3271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
                    v___x_3274_ = v_reuseFailAlloc_3275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3274_;
            }
            5 => {
                v___x_3281_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0;
                v___x_3282_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3282_, 0, v_a_3277_);
                crate::leanh::lean_ctor_set(v___x_3282_, 1, v___x_3281_);
                if v_isShared_3280_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3279_, 0, v___x_3282_);
                    v___x_3284_ = v___x_3279_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
                    v___x_3284_ = v_reuseFailAlloc_3285_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3284_;
            }
            7 => {
                if v_isShared_3290_ == 0 {
                    v___x_3292_ = v___x_3289_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
                    v___x_3292_ = v_reuseFailAlloc_3293_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(
    mut v_info_3295_: *mut crate::leanh::LeanObject,
    mut v_keepUnused_3296_: *mut crate::leanh::LeanObject,
    mut v_a_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
    mut v_a_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keepUnused_boxed_3302_: u8 = 0;
    let mut v_res_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keepUnused_boxed_3302_ = (crate::leanh::lean_unbox(v_keepUnused_3296_) as u8);
    v_res_3303_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(
        v_info_3295_,
        v_keepUnused_boxed_3302_,
        v_a_3297_,
        v_a_3298_,
        v_a_3299_,
        v_a_3300_,
    );
    crate::leanh::lean_dec(v_a_3300_);
    crate::leanh::lean_dec_ref(v_a_3299_);
    crate::leanh::lean_dec(v_a_3298_);
    crate::leanh::lean_dec_ref(v_a_3297_);
    crate::leanh::lean_dec_ref(v_info_3295_);
    return v_res_3303_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3307_ = crate::leanh::lean_box(0);
    v___x_3308_ = l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1;
    v___x_3309_ = l_Lean_Expr_const___override(v___x_3308_, v___x_3307_);
    return v___x_3309_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3310_ = 0;
    v___x_3311_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once),
        _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2,
    );
    v___x_3312_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3312_, 0, v___x_3311_);
    crate::leanh::lean_ctor_set(v___x_3312_, 1, v___x_3311_);
    crate::leanh::lean_ctor_set(v___x_3312_, 2, v___x_3311_);
    crate::leanh::lean_ctor_set(v___x_3312_, 3, v___x_3311_);
    crate::leanh::lean_ctor_set(v___x_3312_, 4, v___x_3311_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3312_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_3310_,
    );
    return v___x_3312_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpHaveResult_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3313_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once),
        _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3,
    );
    return v___x_3313_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
    return v___x_3314_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(
    mut v_toApplicative_3331_: *mut crate::leanh::LeanObject,
    mut v_level_3332_: *mut crate::leanh::LeanObject,
    mut v_exprType_3333_: *mut crate::leanh::LeanObject,
    mut v_e_3334_: *mut crate::leanh::LeanObject,
    mut v___x_3335_: u8,
    mut v_xs_3336_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v_arg_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: u8 = 0;
    let mut v_arg_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: u8 = 0;
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: u8 = 0;
    let mut v_arg_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: u8 = 0;
    let mut v_arg_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: u8 = 0;
    let mut v_arg_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: u8 = 0;
    let mut v_arg_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3382_: u8 = 0;
    let mut v_toPure_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: u8 = 0;
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_3337_) == 0 {
                    v_toPure_3338_ = crate::leanh::lean_ctor_get(v_toApplicative_3331_, 1);
                    crate::leanh::lean_inc(v_toPure_3338_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3331_);
                    v___x_3339_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2;
                    v___x_3340_ = crate::leanh::lean_box(0);
                    v___x_3341_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3341_, 0, v_level_3332_);
                    crate::leanh::lean_ctor_set(v___x_3341_, 1, v___x_3340_);
                    v___x_3342_ = l_Lean_mkConst(v___x_3339_, v___x_3341_);
                    crate::leanh::lean_inc_ref_n(v_e_3334_, 3);
                    crate::leanh::lean_inc_ref(v_exprType_3333_);
                    v_proof_3343_ = l_Lean_mkAppB(v___x_3342_, v_exprType_3333_, v_e_3334_);
                    v___x_3344_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3344_, 0, v_e_3334_);
                    crate::leanh::lean_ctor_set(v___x_3344_, 1, v_exprType_3333_);
                    crate::leanh::lean_ctor_set(v___x_3344_, 2, v_e_3334_);
                    crate::leanh::lean_ctor_set(v___x_3344_, 3, v_e_3334_);
                    crate::leanh::lean_ctor_set(v___x_3344_, 4, v_proof_3343_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3344_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        v___x_3335_,
                    );
                    v___x_3345_ = crate::leanh::lean_apply_2(
                        v_toPure_3338_,
                        crate::leanh::lean_box(0),
                        v___x_3344_,
                    );
                    return v___x_3345_;
                } else {
                    crate::leanh::lean_dec(v_level_3332_);
                    v_e_3346_ = crate::leanh::lean_ctor_get(v_____do__lift_3337_, 0);
                    v_h_3347_ = crate::leanh::lean_ctor_get(v_____do__lift_3337_, 1);
                    v_expr_3348_ = lean_expr_abstract(v_e_3346_, v_xs_3336_);
                    v_proof_3349_ = lean_expr_abstract(v_h_3347_, v_xs_3336_);
                    crate::leanh::lean_inc_ref(v_proof_3349_);
                    v___x_3355_ = l_Lean_Expr_cleanupAnnotations(v_proof_3349_);
                    v___x_3356_ = l_Lean_Expr_isApp(v___x_3355_);
                    if v___x_3356_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3355_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_3357_ = crate::leanh::lean_ctor_get(v___x_3355_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3357_);
                        v___x_3358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3355_);
                        v___x_3359_ = l_Lean_Expr_isApp(v___x_3358_);
                        if v___x_3359_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3358_);
                            crate::leanh::lean_dec_ref(v_arg_3357_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_3360_ = crate::leanh::lean_ctor_get(v___x_3358_, 1);
                            crate::leanh::lean_inc_ref(v_arg_3360_);
                            v___x_3361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3358_);
                            v___x_3362_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4;
                            v___x_3363_ = l_Lean_Expr_isConstOf(v___x_3361_, v___x_3362_);
                            crate::leanh::lean_dec_ref(v___x_3361_);
                            if v___x_3363_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_3360_);
                                crate::leanh::lean_dec_ref(v_arg_3357_);
                                state = 1;
                                continue;
                            } else {
                                v___x_3364_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5;
                                v___x_3365_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_3366_ =
                                    l_Lean_Expr_isAppOfArity(v_arg_3360_, v___x_3364_, v___x_3365_);
                                crate::leanh::lean_dec_ref(v_arg_3360_);
                                if v___x_3366_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_3357_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3367_ = l_Lean_Expr_cleanupAnnotations(v_arg_3357_);
                                    v___x_3368_ = l_Lean_Expr_isApp(v___x_3367_);
                                    if v___x_3368_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_3367_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_3369_ = crate::leanh::lean_ctor_get(v___x_3367_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_3369_);
                                        v___x_3370_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3367_);
                                        v___x_3371_ = l_Lean_Expr_isApp(v___x_3370_);
                                        if v___x_3371_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_3370_);
                                            crate::leanh::lean_dec_ref(v_arg_3369_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_3372_ =
                                                crate::leanh::lean_ctor_get(v___x_3370_, 1);
                                            crate::leanh::lean_inc_ref(v_arg_3372_);
                                            v___x_3373_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3370_);
                                            v___x_3374_ =
                                                l_Lean_Expr_isConstOf(v___x_3373_, v___x_3362_);
                                            crate::leanh::lean_dec_ref(v___x_3373_);
                                            if v___x_3374_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_3372_);
                                                crate::leanh::lean_dec_ref(v_arg_3369_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_3375_ =
                                                    l_Lean_Expr_cleanupAnnotations(v_arg_3372_);
                                                v___x_3376_ = l_Lean_Expr_isApp(v___x_3375_);
                                                if v___x_3376_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_3375_);
                                                    crate::leanh::lean_dec_ref(v_arg_3369_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v_arg_3377_ =
                                                        crate::leanh::lean_ctor_get(v___x_3375_, 1);
                                                    crate::leanh::lean_inc_ref(v_arg_3377_);
                                                    v___x_3378_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_3375_,
                                                    );
                                                    v___x_3379_ = l_Lean_Expr_isApp(v___x_3378_);
                                                    if v___x_3379_ == 0 {
                                                        crate::leanh::lean_dec_ref(v___x_3378_);
                                                        crate::leanh::lean_dec_ref(v_arg_3377_);
                                                        crate::leanh::lean_dec_ref(v_arg_3369_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v_arg_3380_ = crate::leanh::lean_ctor_get(
                                                            v___x_3378_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_arg_3380_);
                                                        v___x_3386_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_3378_,
                                                            );
                                                        v___x_3387_ =
                                                            l_Lean_Expr_isApp(v___x_3386_);
                                                        if v___x_3387_ == 0 {
                                                            crate::leanh::lean_dec_ref(v___x_3386_);
                                                            crate::leanh::lean_dec_ref(v_arg_3380_);
                                                            crate::leanh::lean_dec_ref(v_arg_3377_);
                                                            crate::leanh::lean_dec_ref(v_arg_3369_);
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_3388_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_3386_,
                                                                );
                                                            v___x_3389_ = l_Lean_Expr_isConstOf(
                                                                v___x_3388_,
                                                                v___x_3364_,
                                                            );
                                                            crate::leanh::lean_dec_ref(v___x_3388_);
                                                            if v___x_3389_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3380_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3377_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3369_,
                                                                );
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_3390_ = l_Lean_Expr_getAppFn(
                                                                    v_arg_3369_,
                                                                );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_3390_,
                                                                ) == 4
                                                                {
                                                                    v_declName_3391_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3390_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_declName_3391_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_3390_, 2);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v_declName_3391_,
                                                                    ) == 1
                                                                    {
                                                                        v_pre_3392_ = crate::leanh::lean_ctor_get(v_declName_3391_, 0);
                                                                        if crate::leanh::lean_obj_tag(v_pre_3392_) == 0 {
v_str_3393_ = crate::leanh::lean_ctor_get(v_declName_3391_, 1);
crate::leanh::lean_inc_ref(v_str_3393_);
crate::leanh::lean_dec_ref_known(v_declName_3391_, 2);
v___x_3394_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6;
v___x_3395_ = lean_string_dec_eq(v_str_3393_, v___x_3394_);
if v___x_3395_ == 0 {
v___x_3396_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7;
v___x_3397_ = lean_string_dec_eq(v_str_3393_, v___x_3396_);
if v___x_3397_ == 0 {
v___x_3398_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8;
v___x_3399_ = lean_string_dec_eq(v_str_3393_, v___x_3398_);
if v___x_3399_ == 0 {
v___x_3400_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9;
v___x_3401_ = lean_string_dec_eq(v_str_3393_, v___x_3400_);
if v___x_3401_ == 0 {
v___x_3402_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10;
v___x_3403_ = lean_string_dec_eq(v_str_3393_, v___x_3402_);
if v___x_3403_ == 0 {
v___x_3404_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11;
v___x_3405_ = lean_string_dec_eq(v_str_3393_, v___x_3404_);
crate::leanh::lean_dec_ref(v_str_3393_);
if v___x_3405_ == 0 {
crate::leanh::lean_dec_ref(v_arg_3380_);
crate::leanh::lean_dec_ref(v_arg_3377_);
crate::leanh::lean_dec_ref(v_arg_3369_);
state = 1; continue;
} else {
v___y_3382_ = v___x_3363_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v_str_3393_);
v___y_3382_ = v___x_3363_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v_str_3393_);
v___y_3382_ = v___x_3363_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v_str_3393_);
v___y_3382_ = v___x_3363_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v_str_3393_);
v___y_3382_ = v___x_3363_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref(v_str_3393_);
v___y_3382_ = v___x_3363_;
state = 2; continue;
}
} else {
crate::leanh::lean_dec_ref_known(v_declName_3391_, 2);
crate::leanh::lean_dec_ref(v_arg_3380_);
crate::leanh::lean_dec_ref(v_arg_3377_);
crate::leanh::lean_dec_ref(v_arg_3369_);
state = 1; continue;
}
                                                                    } else {
                                                                        crate::leanh::lean_dec(
                                                                            v_declName_3391_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3380_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3377_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3369_,
                                                                        );
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_3390_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3380_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3377_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3369_,
                                                                    );
                                                                    state = 1;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_toPure_3351_ = crate::leanh::lean_ctor_get(v_toApplicative_3331_, 1);
                crate::leanh::lean_inc(v_toPure_3351_);
                crate::leanh::lean_dec_ref(v_toApplicative_3331_);
                v___x_3352_ = 1;
                crate::leanh::lean_inc_ref(v_expr_3348_);
                v___x_3353_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3353_, 0, v_expr_3348_);
                crate::leanh::lean_ctor_set(v___x_3353_, 1, v_exprType_3333_);
                crate::leanh::lean_ctor_set(v___x_3353_, 2, v_e_3334_);
                crate::leanh::lean_ctor_set(v___x_3353_, 3, v_expr_3348_);
                crate::leanh::lean_ctor_set(v___x_3353_, 4, v_proof_3349_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3353_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_3352_,
                );
                v___x_3354_ = crate::leanh::lean_apply_2(
                    v_toPure_3351_,
                    crate::leanh::lean_box(0),
                    v___x_3353_,
                );
                return v___x_3354_;
            }
            2 => {
                if v___y_3382_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_3380_);
                    crate::leanh::lean_dec_ref(v_arg_3377_);
                    crate::leanh::lean_dec_ref(v_arg_3369_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_proof_3349_);
                    crate::leanh::lean_dec_ref(v_e_3334_);
                    v_toPure_3383_ = crate::leanh::lean_ctor_get(v_toApplicative_3331_, 1);
                    crate::leanh::lean_inc(v_toPure_3383_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3331_);
                    v___x_3384_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3384_, 0, v_arg_3377_);
                    crate::leanh::lean_ctor_set(v___x_3384_, 1, v_exprType_3333_);
                    crate::leanh::lean_ctor_set(v___x_3384_, 2, v_arg_3380_);
                    crate::leanh::lean_ctor_set(v___x_3384_, 3, v_expr_3348_);
                    crate::leanh::lean_ctor_set(v___x_3384_, 4, v_arg_3369_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3384_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        v___x_3363_,
                    );
                    v___x_3385_ = crate::leanh::lean_apply_2(
                        v_toPure_3383_,
                        crate::leanh::lean_box(0),
                        v___x_3384_,
                    );
                    return v___x_3385_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(
    mut v_toApplicative_3406_: *mut crate::leanh::LeanObject,
    mut v_level_3407_: *mut crate::leanh::LeanObject,
    mut v_exprType_3408_: *mut crate::leanh::LeanObject,
    mut v_e_3409_: *mut crate::leanh::LeanObject,
    mut v___x_3410_: *mut crate::leanh::LeanObject,
    mut v_xs_3411_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12297__boxed_3413_: u8 = 0;
    let mut v_res_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12297__boxed_3413_ = (crate::leanh::lean_unbox(v___x_3410_) as u8);
    v_res_3414_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(
            v_toApplicative_3406_,
            v_level_3407_,
            v_exprType_3408_,
            v_e_3409_,
            v___x_12297__boxed_3413_,
            v_xs_3411_,
            v_____do__lift_3412_,
        );
    crate::leanh::lean_dec(v_____do__lift_3412_);
    crate::leanh::lean_dec_ref(v_xs_3411_);
    return v_res_3414_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(
    mut v_inst_3415_: *mut crate::leanh::LeanObject,
    mut v_bodyType_3416_: *mut crate::leanh::LeanObject,
    mut v_xs_3417_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3418_: *mut crate::leanh::LeanObject,
    mut v_level_3419_: *mut crate::leanh::LeanObject,
    mut v_e_3420_: *mut crate::leanh::LeanObject,
    mut v___x_3421_: u8,
    mut v_body_3422_: *mut crate::leanh::LeanObject,
    mut v_toBind_3423_: *mut crate::leanh::LeanObject,
    mut v_____r_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_simp_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprType_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_simp_3425_ = crate::leanh::lean_ctor_get(v_inst_3415_, 2);
    crate::leanh::lean_inc(v_simp_3425_);
    crate::leanh::lean_dec_ref(v_inst_3415_);
    v_exprType_3426_ = lean_expr_abstract(v_bodyType_3416_, v_xs_3417_);
    v___x_3427_ = crate::leanh::lean_box((v___x_3421_) as usize);
    v___f_3428_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 6);
    crate::leanh::lean_closure_set(v___f_3428_, 0, v_toApplicative_3418_);
    crate::leanh::lean_closure_set(v___f_3428_, 1, v_level_3419_);
    crate::leanh::lean_closure_set(v___f_3428_, 2, v_exprType_3426_);
    crate::leanh::lean_closure_set(v___f_3428_, 3, v_e_3420_);
    crate::leanh::lean_closure_set(v___f_3428_, 4, v___x_3427_);
    crate::leanh::lean_closure_set(v___f_3428_, 5, v_xs_3417_);
    v___x_3429_ = crate::leanh::lean_apply_1(v_simp_3425_, v_body_3422_);
    v___x_3430_ = crate::leanh::lean_apply_4(
        v_toBind_3423_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3429_,
        v___f_3428_,
    );
    return v___x_3430_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(
    mut v_inst_3431_: *mut crate::leanh::LeanObject,
    mut v_bodyType_3432_: *mut crate::leanh::LeanObject,
    mut v_xs_3433_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3434_: *mut crate::leanh::LeanObject,
    mut v_level_3435_: *mut crate::leanh::LeanObject,
    mut v_e_3436_: *mut crate::leanh::LeanObject,
    mut v___x_3437_: *mut crate::leanh::LeanObject,
    mut v_body_3438_: *mut crate::leanh::LeanObject,
    mut v_toBind_3439_: *mut crate::leanh::LeanObject,
    mut v_____r_3440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12450__boxed_3441_: u8 = 0;
    let mut v_res_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12450__boxed_3441_ = (crate::leanh::lean_unbox(v___x_3437_) as u8);
    v_res_3442_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(
            v_inst_3431_,
            v_bodyType_3432_,
            v_xs_3433_,
            v_toApplicative_3434_,
            v_level_3435_,
            v_e_3436_,
            v___x_12450__boxed_3441_,
            v_body_3438_,
            v_toBind_3439_,
            v_____r_3440_,
        );
    crate::leanh::lean_dec_ref(v_bodyType_3432_);
    return v_res_3442_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3449_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4;
    v___x_3450_ = l_Lean_stringToMessageData(v___x_3449_);
    return v___x_3450_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(
    mut v_cls_3451_: *mut crate::leanh::LeanObject,
    mut v___x_3452_: *mut crate::leanh::LeanObject,
    mut v___f_3453_: *mut crate::leanh::LeanObject,
    mut v_body_3454_: *mut crate::leanh::LeanObject,
    mut v___x_3455_: *mut crate::leanh::LeanObject,
    mut v___x_3456_: *mut crate::leanh::LeanObject,
    mut v___y_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3466_: u8 = 0;
    let mut v_inheritedTraceOptions_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: u8 = 0;
    let mut v___f_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11852__overap_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3465_ = crate::leanh::lean_ctor_get(v___y_3459_, 2);
                v_hasTrace_3466_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3465_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3466_ == 0 {
                    crate::leanh::lean_dec(v___y_3460_);
                    crate::leanh::lean_dec_ref(v___y_3459_);
                    crate::leanh::lean_dec(v___y_3458_);
                    crate::leanh::lean_dec_ref(v___y_3457_);
                    crate::leanh::lean_dec_ref(v___x_3456_);
                    crate::leanh::lean_dec_ref(v___x_3455_);
                    crate::leanh::lean_dec_ref(v_body_3454_);
                    crate::leanh::lean_dec(v___f_3453_);
                    crate::leanh::lean_dec(v___x_3452_);
                    crate::leanh::lean_dec(v_cls_3451_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_3467_ = crate::leanh::lean_ctor_get(v___y_3459_, 13);
                    v___x_3468_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1;
                    crate::leanh::lean_inc(v_cls_3451_);
                    v___x_3469_ = l_Lean_Name_append(v___x_3468_, v_cls_3451_);
                    v___x_3470_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3467_,
                        v_options_3465_,
                        v___x_3469_,
                    );
                    crate::leanh::lean_dec(v___x_3469_);
                    if v___x_3470_ == 0 {
                        crate::leanh::lean_dec(v___y_3460_);
                        crate::leanh::lean_dec_ref(v___y_3459_);
                        crate::leanh::lean_dec(v___y_3458_);
                        crate::leanh::lean_dec_ref(v___y_3457_);
                        crate::leanh::lean_dec_ref(v___x_3456_);
                        crate::leanh::lean_dec_ref(v___x_3455_);
                        crate::leanh::lean_dec_ref(v_body_3454_);
                        crate::leanh::lean_dec(v___f_3453_);
                        crate::leanh::lean_dec(v___x_3452_);
                        crate::leanh::lean_dec(v_cls_3451_);
                        state = 1;
                        continue;
                    } else {
                        v___f_3471_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2;
                        v___x_3472_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3;
                        v___x_3473_ = l_Lean_Core_instMonadQuotationCoreM;
                        v___x_3474_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                            v___x_3472_,
                            v___x_3452_,
                            v___x_3473_,
                        );
                        v___x_3475_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                            v___f_3471_,
                            v___f_3453_,
                            v___x_3474_,
                        );
                        v_toMonadRef_3476_ = crate::leanh::lean_ctor_get(v___x_3475_, 0);
                        crate::leanh::lean_inc_ref(v_toMonadRef_3476_);
                        crate::leanh::lean_dec_ref(v___x_3475_);
                        v___x_3477_ = l_Lean_Meta_instAddMessageContextMetaM;
                        v___x_3478_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5);
                        v___x_3479_ = l_Lean_MessageData_ofExpr(v_body_3454_);
                        v___x_3480_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3480_, 0, v___x_3478_);
                        crate::leanh::lean_ctor_set(v___x_3480_, 1, v___x_3479_);
                        v___x_11852__overap_3481_ = l_Lean_addTrace___redArg(
                            v___x_3455_,
                            v___x_3456_,
                            v_toMonadRef_3476_,
                            v___x_3477_,
                            v_cls_3451_,
                            v___x_3480_,
                        );
                        v___x_3482_ = crate::leanh::lean_apply_5(
                            v___x_11852__overap_3481_,
                            v___y_3457_,
                            v___y_3458_,
                            v___y_3459_,
                            v___y_3460_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3482_;
                    }
                }
            }
            1 => {
                v___x_3463_ = crate::leanh::lean_box(0);
                v___x_3464_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3463_);
                return v___x_3464_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(
    mut v_cls_3483_: *mut crate::leanh::LeanObject,
    mut v___x_3484_: *mut crate::leanh::LeanObject,
    mut v___f_3485_: *mut crate::leanh::LeanObject,
    mut v_body_3486_: *mut crate::leanh::LeanObject,
    mut v___x_3487_: *mut crate::leanh::LeanObject,
    mut v___x_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3494_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(
            v_cls_3483_,
            v___x_3484_,
            v___f_3485_,
            v_body_3486_,
            v___x_3487_,
            v___x_3488_,
            v___y_3489_,
            v___y_3490_,
            v___y_3491_,
            v___y_3492_,
        );
    return v_res_3494_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(
    mut v_declName_3497_: *mut crate::leanh::LeanObject,
    mut v_type_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v_value_3500_: *mut crate::leanh::LeanObject,
    mut v_nondep_3501_: u8,
    mut v_toApplicative_3502_: *mut crate::leanh::LeanObject,
    mut v___x_3503_: *mut crate::leanh::LeanObject,
    mut v___y_3504_: u8,
    mut v_us_3505_: *mut crate::leanh::LeanObject,
    mut v_rb_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expr_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprType_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprInit_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprResult_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_3512_: u8 = 0;
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprType_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprInit_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprResult_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_expr_3507_ = crate::leanh::lean_ctor_get(v_rb_3506_, 0);
                v_exprType_3508_ = crate::leanh::lean_ctor_get(v_rb_3506_, 1);
                v_exprInit_3509_ = crate::leanh::lean_ctor_get(v_rb_3506_, 2);
                v_exprResult_3510_ = crate::leanh::lean_ctor_get(v_rb_3506_, 3);
                v_proof_3511_ = crate::leanh::lean_ctor_get(v_rb_3506_, 4);
                v_modified_3512_ = crate::leanh::lean_ctor_get_uint8(
                    v_rb_3506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                );
                v_isSharedCheck_3541_ = (!crate::leanh::lean_is_exclusive(v_rb_3506_)) as u8;
                if v_isSharedCheck_3541_ == 0 {
                    v___x_3514_ = v_rb_3506_;
                    v_isShared_3515_ = v_isSharedCheck_3541_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_3511_);
                    crate::leanh::lean_inc(v_exprResult_3510_);
                    crate::leanh::lean_inc(v_exprInit_3509_);
                    crate::leanh::lean_inc(v_exprType_3508_);
                    crate::leanh::lean_inc(v_expr_3507_);
                    crate::leanh::lean_dec(v_rb_3506_);
                    v___x_3514_ = crate::leanh::lean_box(0);
                    v_isShared_3515_ = v_isSharedCheck_3541_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3516_ = 0;
                crate::leanh::lean_inc_ref_n(v_type_3498_, 4);
                crate::leanh::lean_inc_n(v_declName_3497_, 4);
                v___x_3517_ =
                    l_Lean_mkLambda(v_declName_3497_, v___x_3516_, v_type_3498_, v_expr_3507_);
                crate::leanh::lean_inc_ref_n(v___y_3499_, 3);
                crate::leanh::lean_inc_ref(v___x_3517_);
                v_expr_3518_ = l_Lean_Expr_app___override(v___x_3517_, v___y_3499_);
                v___x_3519_ = l_Lean_mkLambda(
                    v_declName_3497_,
                    v___x_3516_,
                    v_type_3498_,
                    v_exprType_3508_,
                );
                crate::leanh::lean_inc_ref(v___x_3519_);
                v_exprType_3520_ = l_Lean_Expr_app___override(v___x_3519_, v___y_3499_);
                v___x_3521_ = l_Lean_mkLambda(
                    v_declName_3497_,
                    v___x_3516_,
                    v_type_3498_,
                    v_exprInit_3509_,
                );
                crate::leanh::lean_inc_ref(v___x_3521_);
                v_exprInit_3522_ = l_Lean_Expr_app___override(v___x_3521_, v_value_3500_);
                v_exprResult_3523_ = l_Lean_Expr_letE___override(
                    v_declName_3497_,
                    v_type_3498_,
                    v___y_3499_,
                    v_exprResult_3510_,
                    v_nondep_3501_,
                );
                if v_modified_3512_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3521_);
                    crate::leanh::lean_dec_ref(v___x_3519_);
                    crate::leanh::lean_dec_ref(v___x_3517_);
                    crate::leanh::lean_dec_ref(v_proof_3511_);
                    crate::leanh::lean_dec(v_us_3505_);
                    crate::leanh::lean_dec_ref(v___y_3499_);
                    crate::leanh::lean_dec_ref(v_type_3498_);
                    crate::leanh::lean_dec(v_declName_3497_);
                    v_toPure_3524_ = crate::leanh::lean_ctor_get(v_toApplicative_3502_, 1);
                    crate::leanh::lean_inc(v_toPure_3524_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3502_);
                    v___x_3525_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2;
                    v___x_3526_ = l_Lean_mkConst(v___x_3525_, v___x_3503_);
                    crate::leanh::lean_inc_ref(v_expr_3518_);
                    crate::leanh::lean_inc_ref(v_exprType_3520_);
                    v_proof_3527_ = l_Lean_mkAppB(v___x_3526_, v_exprType_3520_, v_expr_3518_);
                    if v_isShared_3515_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3514_, 4, v_proof_3527_);
                        crate::leanh::lean_ctor_set(v___x_3514_, 3, v_exprResult_3523_);
                        crate::leanh::lean_ctor_set(v___x_3514_, 2, v_exprInit_3522_);
                        crate::leanh::lean_ctor_set(v___x_3514_, 1, v_exprType_3520_);
                        crate::leanh::lean_ctor_set(v___x_3514_, 0, v_expr_3518_);
                        v___x_3529_ = v___x_3514_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3531_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_expr_3518_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_exprType_3520_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_exprInit_3522_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3531_, 3, v_exprResult_3523_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3531_, 4, v_proof_3527_);
                        v___x_3529_ = v_reuseFailAlloc_3531_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3503_);
                    v_toPure_3532_ = crate::leanh::lean_ctor_get(v_toApplicative_3502_, 1);
                    crate::leanh::lean_inc(v_toPure_3532_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3502_);
                    crate::leanh::lean_inc_ref(v_type_3498_);
                    v___x_3533_ =
                        l_Lean_mkLambda(v_declName_3497_, v___x_3516_, v_type_3498_, v_proof_3511_);
                    v___x_3534_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0;
                    v___x_3535_ = l_Lean_mkConst(v___x_3534_, v_us_3505_);
                    v_proof_3536_ = l_Lean_mkApp6(
                        v___x_3535_,
                        v_type_3498_,
                        v___x_3519_,
                        v___y_3499_,
                        v___x_3521_,
                        v___x_3517_,
                        v___x_3533_,
                    );
                    if v_isShared_3515_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3514_, 4, v_proof_3536_);
                        crate::leanh::lean_ctor_set(v___x_3514_, 3, v_exprResult_3523_);
                        crate::leanh::lean_ctor_set(v___x_3514_, 2, v_exprInit_3522_);
                        crate::leanh::lean_ctor_set(v___x_3514_, 1, v_exprType_3520_);
                        crate::leanh::lean_ctor_set(v___x_3514_, 0, v_expr_3518_);
                        v___x_3538_ = v___x_3514_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3540_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_expr_3518_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_exprType_3520_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 2, v_exprInit_3522_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 3, v_exprResult_3523_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 4, v_proof_3536_);
                        v___x_3538_ = v_reuseFailAlloc_3540_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3529_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_3504_,
                );
                v___x_3530_ = crate::leanh::lean_apply_2(
                    v_toPure_3524_,
                    crate::leanh::lean_box(0),
                    v___x_3529_,
                );
                return v___x_3530_;
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3538_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_nondep_3501_,
                );
                v___x_3539_ = crate::leanh::lean_apply_2(
                    v_toPure_3532_,
                    crate::leanh::lean_box(0),
                    v___x_3538_,
                );
                return v___x_3539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(
    mut v_declName_3542_: *mut crate::leanh::LeanObject,
    mut v_type_3543_: *mut crate::leanh::LeanObject,
    mut v___y_3544_: *mut crate::leanh::LeanObject,
    mut v_value_3545_: *mut crate::leanh::LeanObject,
    mut v_nondep_3546_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3547_: *mut crate::leanh::LeanObject,
    mut v___x_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
    mut v_us_3550_: *mut crate::leanh::LeanObject,
    mut v_rb_3551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_12566__boxed_3552_: u8 = 0;
    let mut v___y_12568__boxed_3553_: u8 = 0;
    let mut v_res_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_12566__boxed_3552_ = (crate::leanh::lean_unbox(v_nondep_3546_) as u8);
    v___y_12568__boxed_3553_ = (crate::leanh::lean_unbox(v___y_3549_) as u8);
    v_res_3554_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(
            v_declName_3542_,
            v_type_3543_,
            v___y_3544_,
            v_value_3545_,
            v_nondep_12566__boxed_3552_,
            v_toApplicative_3547_,
            v___x_3548_,
            v___y_12568__boxed_3553_,
            v_us_3550_,
            v_rb_3551_,
        );
    return v_res_3554_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(
    mut v___f_3555_: *mut crate::leanh::LeanObject,
    mut v_____x_3556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3557_ = crate::leanh::lean_apply_1(v___f_3555_, v_____x_3556_);
    return v___x_3557_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(
    mut v___x_3562_: *mut crate::leanh::LeanObject,
    mut v_declName_3563_: *mut crate::leanh::LeanObject,
    mut v_type_3564_: *mut crate::leanh::LeanObject,
    mut v_value_3565_: *mut crate::leanh::LeanObject,
    mut v_us_3566_: *mut crate::leanh::LeanObject,
    mut v___x_3567_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3568_: *mut crate::leanh::LeanObject,
    mut v_nondep_3569_: u8,
    mut v_rb_3570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expr_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprType_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprInit_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprResult_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_3576_: u8 = 0;
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3579_: u8 = 0;
    let mut v_expr_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprType_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprInit_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprResult_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_expr_3571_ = crate::leanh::lean_ctor_get(v_rb_3570_, 0);
                v_exprType_3572_ = crate::leanh::lean_ctor_get(v_rb_3570_, 1);
                v_exprInit_3573_ = crate::leanh::lean_ctor_get(v_rb_3570_, 2);
                v_exprResult_3574_ = crate::leanh::lean_ctor_get(v_rb_3570_, 3);
                v_proof_3575_ = crate::leanh::lean_ctor_get(v_rb_3570_, 4);
                v_modified_3576_ = crate::leanh::lean_ctor_get_uint8(
                    v_rb_3570_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                );
                v_isSharedCheck_3606_ = (!crate::leanh::lean_is_exclusive(v_rb_3570_)) as u8;
                if v_isSharedCheck_3606_ == 0 {
                    v___x_3578_ = v_rb_3570_;
                    v_isShared_3579_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_3575_);
                    crate::leanh::lean_inc(v_exprResult_3574_);
                    crate::leanh::lean_inc(v_exprInit_3573_);
                    crate::leanh::lean_inc(v_exprType_3572_);
                    crate::leanh::lean_inc(v_expr_3571_);
                    crate::leanh::lean_dec(v_rb_3570_);
                    v___x_3578_ = crate::leanh::lean_box(0);
                    v_isShared_3579_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_expr_3580_ = lean_expr_lower_loose_bvars(v_expr_3571_, v___x_3562_, v___x_3562_);
                crate::leanh::lean_dec_ref(v_expr_3571_);
                v_exprType_3581_ =
                    lean_expr_lower_loose_bvars(v_exprType_3572_, v___x_3562_, v___x_3562_);
                crate::leanh::lean_dec_ref(v_exprType_3572_);
                v___x_3582_ = 0;
                crate::leanh::lean_inc_ref(v_type_3564_);
                crate::leanh::lean_inc(v_declName_3563_);
                v___x_3583_ = l_Lean_mkLambda(
                    v_declName_3563_,
                    v___x_3582_,
                    v_type_3564_,
                    v_exprInit_3573_,
                );
                crate::leanh::lean_inc_ref(v_value_3565_);
                crate::leanh::lean_inc_ref(v___x_3583_);
                v_exprInit_3584_ = l_Lean_Expr_app___override(v___x_3583_, v_value_3565_);
                v_exprResult_3585_ =
                    lean_expr_lower_loose_bvars(v_exprResult_3574_, v___x_3562_, v___x_3562_);
                crate::leanh::lean_dec_ref(v_exprResult_3574_);
                if v_modified_3576_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3583_);
                    crate::leanh::lean_dec_ref(v_proof_3575_);
                    crate::leanh::lean_dec(v_declName_3563_);
                    v___x_3586_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0;
                    v___x_3587_ = l_Lean_mkConst(v___x_3586_, v_us_3566_);
                    v___x_3588_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2;
                    v___x_3589_ = l_Lean_mkConst(v___x_3588_, v___x_3567_);
                    crate::leanh::lean_inc_ref_n(v_expr_3580_, 3);
                    crate::leanh::lean_inc_ref_n(v_exprType_3581_, 2);
                    v___x_3590_ = l_Lean_mkAppB(v___x_3589_, v_exprType_3581_, v_expr_3580_);
                    v_proof_3591_ = l_Lean_mkApp6(
                        v___x_3587_,
                        v_type_3564_,
                        v_exprType_3581_,
                        v_value_3565_,
                        v_expr_3580_,
                        v_expr_3580_,
                        v___x_3590_,
                    );
                    v_toPure_3592_ = crate::leanh::lean_ctor_get(v_toApplicative_3568_, 1);
                    crate::leanh::lean_inc(v_toPure_3592_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3568_);
                    if v_isShared_3579_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3578_, 4, v_proof_3591_);
                        crate::leanh::lean_ctor_set(v___x_3578_, 3, v_exprResult_3585_);
                        crate::leanh::lean_ctor_set(v___x_3578_, 2, v_exprInit_3584_);
                        crate::leanh::lean_ctor_set(v___x_3578_, 1, v_exprType_3581_);
                        crate::leanh::lean_ctor_set(v___x_3578_, 0, v_expr_3580_);
                        v___x_3594_ = v___x_3578_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3596_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_expr_3580_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_exprType_3581_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_exprInit_3584_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_exprResult_3585_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_proof_3591_);
                        v___x_3594_ = v_reuseFailAlloc_3596_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3567_);
                    v_toPure_3597_ = crate::leanh::lean_ctor_get(v_toApplicative_3568_, 1);
                    crate::leanh::lean_inc(v_toPure_3597_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3568_);
                    crate::leanh::lean_inc_ref(v_type_3564_);
                    v___x_3598_ =
                        l_Lean_mkLambda(v_declName_3563_, v___x_3582_, v_type_3564_, v_proof_3575_);
                    v___x_3599_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1;
                    v___x_3600_ = l_Lean_mkConst(v___x_3599_, v_us_3566_);
                    crate::leanh::lean_inc_ref(v_expr_3580_);
                    crate::leanh::lean_inc_ref(v_exprType_3581_);
                    v_proof_3601_ = l_Lean_mkApp6(
                        v___x_3600_,
                        v_type_3564_,
                        v_exprType_3581_,
                        v_value_3565_,
                        v___x_3583_,
                        v_expr_3580_,
                        v___x_3598_,
                    );
                    if v_isShared_3579_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3578_, 4, v_proof_3601_);
                        crate::leanh::lean_ctor_set(v___x_3578_, 3, v_exprResult_3585_);
                        crate::leanh::lean_ctor_set(v___x_3578_, 2, v_exprInit_3584_);
                        crate::leanh::lean_ctor_set(v___x_3578_, 1, v_exprType_3581_);
                        crate::leanh::lean_ctor_set(v___x_3578_, 0, v_expr_3580_);
                        v___x_3603_ = v___x_3578_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3605_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_expr_3580_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_exprType_3581_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 2, v_exprInit_3584_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 3, v_exprResult_3585_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 4, v_proof_3601_);
                        v___x_3603_ = v_reuseFailAlloc_3605_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3594_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_nondep_3569_,
                );
                v___x_3595_ = crate::leanh::lean_apply_2(
                    v_toPure_3592_,
                    crate::leanh::lean_box(0),
                    v___x_3594_,
                );
                return v___x_3595_;
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3603_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_nondep_3569_,
                );
                v___x_3604_ = crate::leanh::lean_apply_2(
                    v_toPure_3597_,
                    crate::leanh::lean_box(0),
                    v___x_3603_,
                );
                return v___x_3604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(
    mut v___x_3607_: *mut crate::leanh::LeanObject,
    mut v_declName_3608_: *mut crate::leanh::LeanObject,
    mut v_type_3609_: *mut crate::leanh::LeanObject,
    mut v_value_3610_: *mut crate::leanh::LeanObject,
    mut v_us_3611_: *mut crate::leanh::LeanObject,
    mut v___x_3612_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3613_: *mut crate::leanh::LeanObject,
    mut v_nondep_3614_: *mut crate::leanh::LeanObject,
    mut v_rb_3615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_12653__boxed_3616_: u8 = 0;
    let mut v_res_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_12653__boxed_3616_ = (crate::leanh::lean_unbox(v_nondep_3614_) as u8);
    v_res_3617_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(
            v___x_3607_,
            v_declName_3608_,
            v_type_3609_,
            v_value_3610_,
            v_us_3611_,
            v___x_3612_,
            v_toApplicative_3613_,
            v_nondep_12653__boxed_3616_,
            v_rb_3615_,
        );
    crate::leanh::lean_dec(v___x_3607_);
    return v_res_3617_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3619_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0;
    v___x_3620_ = l_Lean_stringToMessageData(v___x_3619_);
    return v___x_3620_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3622_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2;
    v___x_3623_ = l_Lean_stringToMessageData(v___x_3622_);
    return v___x_3623_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(
    mut v_cls_3624_: *mut crate::leanh::LeanObject,
    mut v___x_3625_: *mut crate::leanh::LeanObject,
    mut v___f_3626_: *mut crate::leanh::LeanObject,
    mut v_declName_3627_: *mut crate::leanh::LeanObject,
    mut v_val_3628_: *mut crate::leanh::LeanObject,
    mut v___x_3629_: *mut crate::leanh::LeanObject,
    mut v___x_3630_: *mut crate::leanh::LeanObject,
    mut v___y_3631_: *mut crate::leanh::LeanObject,
    mut v___y_3632_: *mut crate::leanh::LeanObject,
    mut v___y_3633_: *mut crate::leanh::LeanObject,
    mut v___y_3634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3640_: u8 = 0;
    let mut v_inheritedTraceOptions_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    let mut v___f_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12263__overap_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3639_ = crate::leanh::lean_ctor_get(v___y_3633_, 2);
                v_hasTrace_3640_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3639_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3640_ == 0 {
                    crate::leanh::lean_dec(v___y_3634_);
                    crate::leanh::lean_dec_ref(v___y_3633_);
                    crate::leanh::lean_dec(v___y_3632_);
                    crate::leanh::lean_dec_ref(v___y_3631_);
                    crate::leanh::lean_dec_ref(v___x_3630_);
                    crate::leanh::lean_dec_ref(v___x_3629_);
                    crate::leanh::lean_dec_ref(v_val_3628_);
                    crate::leanh::lean_dec(v_declName_3627_);
                    crate::leanh::lean_dec(v___f_3626_);
                    crate::leanh::lean_dec(v___x_3625_);
                    crate::leanh::lean_dec(v_cls_3624_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_3641_ = crate::leanh::lean_ctor_get(v___y_3633_, 13);
                    v___x_3642_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1;
                    crate::leanh::lean_inc(v_cls_3624_);
                    v___x_3643_ = l_Lean_Name_append(v___x_3642_, v_cls_3624_);
                    v___x_3644_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3641_,
                        v_options_3639_,
                        v___x_3643_,
                    );
                    crate::leanh::lean_dec(v___x_3643_);
                    if v___x_3644_ == 0 {
                        crate::leanh::lean_dec(v___y_3634_);
                        crate::leanh::lean_dec_ref(v___y_3633_);
                        crate::leanh::lean_dec(v___y_3632_);
                        crate::leanh::lean_dec_ref(v___y_3631_);
                        crate::leanh::lean_dec_ref(v___x_3630_);
                        crate::leanh::lean_dec_ref(v___x_3629_);
                        crate::leanh::lean_dec_ref(v_val_3628_);
                        crate::leanh::lean_dec(v_declName_3627_);
                        crate::leanh::lean_dec(v___f_3626_);
                        crate::leanh::lean_dec(v___x_3625_);
                        crate::leanh::lean_dec(v_cls_3624_);
                        state = 1;
                        continue;
                    } else {
                        v___f_3645_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2;
                        v___x_3646_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3;
                        v___x_3647_ = l_Lean_Core_instMonadQuotationCoreM;
                        v___x_3648_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                            v___x_3646_,
                            v___x_3625_,
                            v___x_3647_,
                        );
                        v___x_3649_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                            v___f_3645_,
                            v___f_3626_,
                            v___x_3648_,
                        );
                        v_toMonadRef_3650_ = crate::leanh::lean_ctor_get(v___x_3649_, 0);
                        crate::leanh::lean_inc_ref(v_toMonadRef_3650_);
                        crate::leanh::lean_dec_ref(v___x_3649_);
                        v___x_3651_ = l_Lean_Meta_instAddMessageContextMetaM;
                        v___x_3652_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
                        v___x_3653_ = l_Lean_MessageData_ofName(v_declName_3627_);
                        v___x_3654_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3654_, 0, v___x_3652_);
                        crate::leanh::lean_ctor_set(v___x_3654_, 1, v___x_3653_);
                        v___x_3655_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
                        v___x_3656_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3656_, 0, v___x_3654_);
                        crate::leanh::lean_ctor_set(v___x_3656_, 1, v___x_3655_);
                        v___x_3657_ = l_Lean_MessageData_ofExpr(v_val_3628_);
                        v___x_3658_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3658_, 0, v___x_3656_);
                        crate::leanh::lean_ctor_set(v___x_3658_, 1, v___x_3657_);
                        v___x_12263__overap_3659_ = l_Lean_addTrace___redArg(
                            v___x_3629_,
                            v___x_3630_,
                            v_toMonadRef_3650_,
                            v___x_3651_,
                            v_cls_3624_,
                            v___x_3658_,
                        );
                        v___x_3660_ = crate::leanh::lean_apply_5(
                            v___x_12263__overap_3659_,
                            v___y_3631_,
                            v___y_3632_,
                            v___y_3633_,
                            v___y_3634_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3660_;
                    }
                }
            }
            1 => {
                v___x_3637_ = crate::leanh::lean_box(0);
                v___x_3638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3638_, 0, v___x_3637_);
                return v___x_3638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(
    mut v_cls_3661_: *mut crate::leanh::LeanObject,
    mut v___x_3662_: *mut crate::leanh::LeanObject,
    mut v___f_3663_: *mut crate::leanh::LeanObject,
    mut v_declName_3664_: *mut crate::leanh::LeanObject,
    mut v_val_3665_: *mut crate::leanh::LeanObject,
    mut v___x_3666_: *mut crate::leanh::LeanObject,
    mut v___x_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3673_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(
            v_cls_3661_,
            v___x_3662_,
            v___f_3663_,
            v_declName_3664_,
            v_val_3665_,
            v___x_3666_,
            v___x_3667_,
            v___y_3668_,
            v___y_3669_,
            v___y_3670_,
            v___y_3671_,
        );
    return v_res_3673_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3675_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0;
    v___x_3676_ = l_Lean_stringToMessageData(v___x_3675_);
    return v___x_3676_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3678_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2;
    v___x_3679_ = l_Lean_stringToMessageData(v___x_3678_);
    return v___x_3679_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(
    mut v_cls_3680_: *mut crate::leanh::LeanObject,
    mut v___x_3681_: *mut crate::leanh::LeanObject,
    mut v___f_3682_: *mut crate::leanh::LeanObject,
    mut v_declName_3683_: *mut crate::leanh::LeanObject,
    mut v_val_3684_: *mut crate::leanh::LeanObject,
    mut v_val_x27_3685_: *mut crate::leanh::LeanObject,
    mut v___x_3686_: *mut crate::leanh::LeanObject,
    mut v___x_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
    mut v___y_3689_: *mut crate::leanh::LeanObject,
    mut v___y_3690_: *mut crate::leanh::LeanObject,
    mut v___y_3691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3697_: u8 = 0;
    let mut v_inheritedTraceOptions_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: u8 = 0;
    let mut v___f_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11945__overap_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3696_ = crate::leanh::lean_ctor_get(v___y_3690_, 2);
                v_hasTrace_3697_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3696_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3697_ == 0 {
                    crate::leanh::lean_dec(v___y_3691_);
                    crate::leanh::lean_dec_ref(v___y_3690_);
                    crate::leanh::lean_dec(v___y_3689_);
                    crate::leanh::lean_dec_ref(v___y_3688_);
                    crate::leanh::lean_dec_ref(v___x_3687_);
                    crate::leanh::lean_dec_ref(v___x_3686_);
                    crate::leanh::lean_dec_ref(v_val_x27_3685_);
                    crate::leanh::lean_dec_ref(v_val_3684_);
                    crate::leanh::lean_dec(v_declName_3683_);
                    crate::leanh::lean_dec(v___f_3682_);
                    crate::leanh::lean_dec(v___x_3681_);
                    crate::leanh::lean_dec(v_cls_3680_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_3698_ = crate::leanh::lean_ctor_get(v___y_3690_, 13);
                    v___x_3699_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1;
                    crate::leanh::lean_inc(v_cls_3680_);
                    v___x_3700_ = l_Lean_Name_append(v___x_3699_, v_cls_3680_);
                    v___x_3701_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3698_,
                        v_options_3696_,
                        v___x_3700_,
                    );
                    crate::leanh::lean_dec(v___x_3700_);
                    if v___x_3701_ == 0 {
                        crate::leanh::lean_dec(v___y_3691_);
                        crate::leanh::lean_dec_ref(v___y_3690_);
                        crate::leanh::lean_dec(v___y_3689_);
                        crate::leanh::lean_dec_ref(v___y_3688_);
                        crate::leanh::lean_dec_ref(v___x_3687_);
                        crate::leanh::lean_dec_ref(v___x_3686_);
                        crate::leanh::lean_dec_ref(v_val_x27_3685_);
                        crate::leanh::lean_dec_ref(v_val_3684_);
                        crate::leanh::lean_dec(v_declName_3683_);
                        crate::leanh::lean_dec(v___f_3682_);
                        crate::leanh::lean_dec(v___x_3681_);
                        crate::leanh::lean_dec(v_cls_3680_);
                        state = 1;
                        continue;
                    } else {
                        v___f_3702_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2;
                        v___x_3703_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3;
                        v___x_3704_ = l_Lean_Core_instMonadQuotationCoreM;
                        v___x_3705_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                            v___x_3703_,
                            v___x_3681_,
                            v___x_3704_,
                        );
                        v___x_3706_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                            v___f_3702_,
                            v___f_3682_,
                            v___x_3705_,
                        );
                        v_toMonadRef_3707_ = crate::leanh::lean_ctor_get(v___x_3706_, 0);
                        crate::leanh::lean_inc_ref(v_toMonadRef_3707_);
                        crate::leanh::lean_dec_ref(v___x_3706_);
                        v___x_3708_ = l_Lean_Meta_instAddMessageContextMetaM;
                        v___x_3709_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
                        v___x_3710_ = l_Lean_MessageData_ofName(v_declName_3683_);
                        v___x_3711_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3711_, 0, v___x_3709_);
                        crate::leanh::lean_ctor_set(v___x_3711_, 1, v___x_3710_);
                        v___x_3712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
                        v___x_3713_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3713_, 0, v___x_3711_);
                        crate::leanh::lean_ctor_set(v___x_3713_, 1, v___x_3712_);
                        v___x_3714_ = l_Lean_MessageData_ofExpr(v_val_3684_);
                        v___x_3715_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3715_, 0, v___x_3713_);
                        crate::leanh::lean_ctor_set(v___x_3715_, 1, v___x_3714_);
                        v___x_3716_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
                        v___x_3717_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3717_, 0, v___x_3715_);
                        crate::leanh::lean_ctor_set(v___x_3717_, 1, v___x_3716_);
                        v___x_3718_ = l_Lean_MessageData_ofExpr(v_val_x27_3685_);
                        v___x_3719_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3719_, 0, v___x_3717_);
                        crate::leanh::lean_ctor_set(v___x_3719_, 1, v___x_3718_);
                        v___x_11945__overap_3720_ = l_Lean_addTrace___redArg(
                            v___x_3686_,
                            v___x_3687_,
                            v_toMonadRef_3707_,
                            v___x_3708_,
                            v_cls_3680_,
                            v___x_3719_,
                        );
                        v___x_3721_ = crate::leanh::lean_apply_5(
                            v___x_11945__overap_3720_,
                            v___y_3688_,
                            v___y_3689_,
                            v___y_3690_,
                            v___y_3691_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3721_;
                    }
                }
            }
            1 => {
                v___x_3694_ = crate::leanh::lean_box(0);
                v___x_3695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3695_, 0, v___x_3694_);
                return v___x_3695_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(
    mut v_cls_3722_: *mut crate::leanh::LeanObject,
    mut v___x_3723_: *mut crate::leanh::LeanObject,
    mut v___f_3724_: *mut crate::leanh::LeanObject,
    mut v_declName_3725_: *mut crate::leanh::LeanObject,
    mut v_val_3726_: *mut crate::leanh::LeanObject,
    mut v_val_x27_3727_: *mut crate::leanh::LeanObject,
    mut v___x_3728_: *mut crate::leanh::LeanObject,
    mut v___x_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
    mut v___y_3734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3735_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(
            v_cls_3722_,
            v___x_3723_,
            v___f_3724_,
            v_declName_3725_,
            v_val_3726_,
            v_val_x27_3727_,
            v___x_3728_,
            v___x_3729_,
            v___y_3730_,
            v___y_3731_,
            v___y_3732_,
            v___y_3733_,
        );
    return v_res_3735_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(
    mut v_toApplicative_3736_: *mut crate::leanh::LeanObject,
    mut v_e_3737_: *mut crate::leanh::LeanObject,
    mut v_xs_3738_: *mut crate::leanh::LeanObject,
    mut v_h_3739_: *mut crate::leanh::LeanObject,
    mut v_nondep_3740_: u8,
    mut v_toBind_3741_: *mut crate::leanh::LeanObject,
    mut v___f_3742_: *mut crate::leanh::LeanObject,
    mut v_____r_3743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_3744_ = crate::leanh::lean_ctor_get(v_toApplicative_3736_, 1);
    crate::leanh::lean_inc(v_toPure_3744_);
    crate::leanh::lean_dec_ref(v_toApplicative_3736_);
    v___x_3745_ = lean_expr_abstract(v_e_3737_, v_xs_3738_);
    v___x_3746_ = lean_expr_abstract(v_h_3739_, v_xs_3738_);
    v___x_3747_ = crate::leanh::lean_box((v_nondep_3740_) as usize);
    v___x_3748_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3748_, 0, v___x_3747_);
    crate::leanh::lean_ctor_set(v___x_3748_, 1, v___x_3746_);
    v___x_3749_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3749_, 0, v___x_3745_);
    crate::leanh::lean_ctor_set(v___x_3749_, 1, v___x_3748_);
    v___x_3750_ =
        crate::leanh::lean_apply_2(v_toPure_3744_, crate::leanh::lean_box(0), v___x_3749_);
    v___x_3751_ = crate::leanh::lean_apply_4(
        v_toBind_3741_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3750_,
        v___f_3742_,
    );
    return v___x_3751_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(
    mut v_toApplicative_3752_: *mut crate::leanh::LeanObject,
    mut v_e_3753_: *mut crate::leanh::LeanObject,
    mut v_xs_3754_: *mut crate::leanh::LeanObject,
    mut v_h_3755_: *mut crate::leanh::LeanObject,
    mut v_nondep_3756_: *mut crate::leanh::LeanObject,
    mut v_toBind_3757_: *mut crate::leanh::LeanObject,
    mut v___f_3758_: *mut crate::leanh::LeanObject,
    mut v_____r_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_12919__boxed_3760_: u8 = 0;
    let mut v_res_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_12919__boxed_3760_ = (crate::leanh::lean_unbox(v_nondep_3756_) as u8);
    v_res_3761_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(
            v_toApplicative_3752_,
            v_e_3753_,
            v_xs_3754_,
            v_h_3755_,
            v_nondep_12919__boxed_3760_,
            v_toBind_3757_,
            v___f_3758_,
            v_____r_3759_,
        );
    crate::leanh::lean_dec_ref(v_h_3755_);
    crate::leanh::lean_dec_ref(v_xs_3754_);
    crate::leanh::lean_dec_ref(v_e_3753_);
    return v_res_3761_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3763_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0;
    v___x_3764_ = l_Lean_stringToMessageData(v___x_3763_);
    return v___x_3764_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(
    mut v_cls_3765_: *mut crate::leanh::LeanObject,
    mut v___x_3766_: *mut crate::leanh::LeanObject,
    mut v___f_3767_: *mut crate::leanh::LeanObject,
    mut v_declName_3768_: *mut crate::leanh::LeanObject,
    mut v_val_3769_: *mut crate::leanh::LeanObject,
    mut v_e_3770_: *mut crate::leanh::LeanObject,
    mut v___x_3771_: *mut crate::leanh::LeanObject,
    mut v___x_3772_: *mut crate::leanh::LeanObject,
    mut v___y_3773_: *mut crate::leanh::LeanObject,
    mut v___y_3774_: *mut crate::leanh::LeanObject,
    mut v___y_3775_: *mut crate::leanh::LeanObject,
    mut v___y_3776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3782_: u8 = 0;
    let mut v_inheritedTraceOptions_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___f_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12125__overap_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3781_ = crate::leanh::lean_ctor_get(v___y_3775_, 2);
                v_hasTrace_3782_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3781_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3782_ == 0 {
                    crate::leanh::lean_dec(v___y_3776_);
                    crate::leanh::lean_dec_ref(v___y_3775_);
                    crate::leanh::lean_dec(v___y_3774_);
                    crate::leanh::lean_dec_ref(v___y_3773_);
                    crate::leanh::lean_dec_ref(v___x_3772_);
                    crate::leanh::lean_dec_ref(v___x_3771_);
                    crate::leanh::lean_dec_ref(v_e_3770_);
                    crate::leanh::lean_dec_ref(v_val_3769_);
                    crate::leanh::lean_dec(v_declName_3768_);
                    crate::leanh::lean_dec(v___f_3767_);
                    crate::leanh::lean_dec(v___x_3766_);
                    crate::leanh::lean_dec(v_cls_3765_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_3783_ = crate::leanh::lean_ctor_get(v___y_3775_, 13);
                    v___x_3784_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1;
                    crate::leanh::lean_inc(v_cls_3765_);
                    v___x_3785_ = l_Lean_Name_append(v___x_3784_, v_cls_3765_);
                    v___x_3786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3783_,
                        v_options_3781_,
                        v___x_3785_,
                    );
                    crate::leanh::lean_dec(v___x_3785_);
                    if v___x_3786_ == 0 {
                        crate::leanh::lean_dec(v___y_3776_);
                        crate::leanh::lean_dec_ref(v___y_3775_);
                        crate::leanh::lean_dec(v___y_3774_);
                        crate::leanh::lean_dec_ref(v___y_3773_);
                        crate::leanh::lean_dec_ref(v___x_3772_);
                        crate::leanh::lean_dec_ref(v___x_3771_);
                        crate::leanh::lean_dec_ref(v_e_3770_);
                        crate::leanh::lean_dec_ref(v_val_3769_);
                        crate::leanh::lean_dec(v_declName_3768_);
                        crate::leanh::lean_dec(v___f_3767_);
                        crate::leanh::lean_dec(v___x_3766_);
                        crate::leanh::lean_dec(v_cls_3765_);
                        state = 1;
                        continue;
                    } else {
                        v___f_3787_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2;
                        v___x_3788_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3;
                        v___x_3789_ = l_Lean_Core_instMonadQuotationCoreM;
                        v___x_3790_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                            v___x_3788_,
                            v___x_3766_,
                            v___x_3789_,
                        );
                        v___x_3791_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                            v___f_3787_,
                            v___f_3767_,
                            v___x_3790_,
                        );
                        v_toMonadRef_3792_ = crate::leanh::lean_ctor_get(v___x_3791_, 0);
                        crate::leanh::lean_inc_ref(v_toMonadRef_3792_);
                        crate::leanh::lean_dec_ref(v___x_3791_);
                        v___x_3793_ = l_Lean_Meta_instAddMessageContextMetaM;
                        v___x_3794_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
                        v___x_3795_ = l_Lean_MessageData_ofName(v_declName_3768_);
                        v___x_3796_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3796_, 0, v___x_3794_);
                        crate::leanh::lean_ctor_set(v___x_3796_, 1, v___x_3795_);
                        v___x_3797_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
                        v___x_3798_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3798_, 0, v___x_3796_);
                        crate::leanh::lean_ctor_set(v___x_3798_, 1, v___x_3797_);
                        v___x_3799_ = l_Lean_MessageData_ofExpr(v_val_3769_);
                        v___x_3800_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3800_, 0, v___x_3798_);
                        crate::leanh::lean_ctor_set(v___x_3800_, 1, v___x_3799_);
                        v___x_3801_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
                        v___x_3802_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3802_, 0, v___x_3800_);
                        crate::leanh::lean_ctor_set(v___x_3802_, 1, v___x_3801_);
                        v___x_3803_ = l_Lean_MessageData_ofExpr(v_e_3770_);
                        v___x_3804_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3804_, 0, v___x_3802_);
                        crate::leanh::lean_ctor_set(v___x_3804_, 1, v___x_3803_);
                        v___x_12125__overap_3805_ = l_Lean_addTrace___redArg(
                            v___x_3771_,
                            v___x_3772_,
                            v_toMonadRef_3792_,
                            v___x_3793_,
                            v_cls_3765_,
                            v___x_3804_,
                        );
                        v___x_3806_ = crate::leanh::lean_apply_5(
                            v___x_12125__overap_3805_,
                            v___y_3773_,
                            v___y_3774_,
                            v___y_3775_,
                            v___y_3776_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3806_;
                    }
                }
            }
            1 => {
                v___x_3779_ = crate::leanh::lean_box(0);
                v___x_3780_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3780_, 0, v___x_3779_);
                return v___x_3780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(
    mut v_cls_3807_: *mut crate::leanh::LeanObject,
    mut v___x_3808_: *mut crate::leanh::LeanObject,
    mut v___f_3809_: *mut crate::leanh::LeanObject,
    mut v_declName_3810_: *mut crate::leanh::LeanObject,
    mut v_val_3811_: *mut crate::leanh::LeanObject,
    mut v_e_3812_: *mut crate::leanh::LeanObject,
    mut v___x_3813_: *mut crate::leanh::LeanObject,
    mut v___x_3814_: *mut crate::leanh::LeanObject,
    mut v___y_3815_: *mut crate::leanh::LeanObject,
    mut v___y_3816_: *mut crate::leanh::LeanObject,
    mut v___y_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3820_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(
            v_cls_3807_,
            v___x_3808_,
            v___f_3809_,
            v_declName_3810_,
            v_val_3811_,
            v_e_3812_,
            v___x_3813_,
            v___x_3814_,
            v___y_3815_,
            v___y_3816_,
            v___y_3817_,
            v___y_3818_,
        );
    return v_res_3820_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3821_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0);
    v___x_3823_ = l_StateRefT_x27_instMonad___redArg(v___x_3822_);
    return v___x_3823_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = l_Lean_Core_instMonadTraceCoreM;
    v___x_3840_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12;
    v___x_3841_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3840_, v___x_3839_);
    return v___x_3841_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3842_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13);
    v___f_3843_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11;
    v___x_3844_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3843_, v___x_3842_);
    return v___x_3844_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(
    mut v_toApplicative_3845_: *mut crate::leanh::LeanObject,
    mut v_level_3846_: *mut crate::leanh::LeanObject,
    mut v___x_3847_: *mut crate::leanh::LeanObject,
    mut v_type_3848_: *mut crate::leanh::LeanObject,
    mut v_value_3849_: *mut crate::leanh::LeanObject,
    mut v___x_3850_: u8,
    mut v_toBind_3851_: *mut crate::leanh::LeanObject,
    mut v___f_3852_: *mut crate::leanh::LeanObject,
    mut v_xs_3853_: *mut crate::leanh::LeanObject,
    mut v_nondep_3854_: u8,
    mut v___f_3855_: *mut crate::leanh::LeanObject,
    mut v_declName_3856_: *mut crate::leanh::LeanObject,
    mut v_val_3857_: *mut crate::leanh::LeanObject,
    mut v_inst_3858_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3874_: u8 = 0;
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v_toFunctor_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3903_: u8 = 0;
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut v_unused_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut v_unused_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_3859_) == 0 {
                    crate::leanh::lean_dec(v_inst_3858_);
                    crate::leanh::lean_dec_ref(v_val_3857_);
                    crate::leanh::lean_dec(v_declName_3856_);
                    crate::leanh::lean_dec(v___f_3855_);
                    crate::leanh::lean_dec_ref(v_xs_3853_);
                    v_toPure_3860_ = crate::leanh::lean_ctor_get(v_toApplicative_3845_, 1);
                    crate::leanh::lean_inc(v_toPure_3860_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3845_);
                    v___x_3861_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2;
                    v___x_3862_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3862_, 0, v_level_3846_);
                    crate::leanh::lean_ctor_set(v___x_3862_, 1, v___x_3847_);
                    v___x_3863_ = l_Lean_mkConst(v___x_3861_, v___x_3862_);
                    crate::leanh::lean_inc_ref(v_value_3849_);
                    v___x_3864_ = l_Lean_mkAppB(v___x_3863_, v_type_3848_, v_value_3849_);
                    v___x_3865_ = crate::leanh::lean_box((v___x_3850_) as usize);
                    v___x_3866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3866_, 0, v___x_3865_);
                    crate::leanh::lean_ctor_set(v___x_3866_, 1, v___x_3864_);
                    v___x_3867_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3867_, 0, v_value_3849_);
                    crate::leanh::lean_ctor_set(v___x_3867_, 1, v___x_3866_);
                    v___x_3868_ = crate::leanh::lean_apply_2(
                        v_toPure_3860_,
                        crate::leanh::lean_box(0),
                        v___x_3867_,
                    );
                    v___x_3869_ = crate::leanh::lean_apply_4(
                        v_toBind_3851_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3868_,
                        v___f_3852_,
                    );
                    return v___x_3869_;
                } else {
                    crate::leanh::lean_dec(v___f_3852_);
                    crate::leanh::lean_dec_ref(v_value_3849_);
                    crate::leanh::lean_dec_ref(v_type_3848_);
                    crate::leanh::lean_dec(v___x_3847_);
                    crate::leanh::lean_dec(v_level_3846_);
                    v_e_3870_ = crate::leanh::lean_ctor_get(v_____do__lift_3859_, 0);
                    v_h_3871_ = crate::leanh::lean_ctor_get(v_____do__lift_3859_, 1);
                    v_isSharedCheck_3932_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_3859_)) as u8;
                    if v_isSharedCheck_3932_ == 0 {
                        v___x_3873_ = v_____do__lift_3859_;
                        v_isShared_3874_ = v_isSharedCheck_3932_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_h_3871_);
                        crate::leanh::lean_inc(v_e_3870_);
                        crate::leanh::lean_dec(v_____do__lift_3859_);
                        v___x_3873_ = crate::leanh::lean_box(0);
                        v_isShared_3874_ = v_isSharedCheck_3932_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3875_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
                v_toApplicative_3876_ = crate::leanh::lean_ctor_get(v___x_3875_, 0);
                v_toFunctor_3877_ = crate::leanh::lean_ctor_get(v_toApplicative_3876_, 0);
                v_toSeq_3878_ = crate::leanh::lean_ctor_get(v_toApplicative_3876_, 2);
                v_toSeqLeft_3879_ = crate::leanh::lean_ctor_get(v_toApplicative_3876_, 3);
                v_toSeqRight_3880_ = crate::leanh::lean_ctor_get(v_toApplicative_3876_, 4);
                v___f_3881_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2;
                v___f_3882_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3877_, 2);
                v___f_3883_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3883_, 0, v_toFunctor_3877_);
                v___f_3884_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3884_, 0, v_toFunctor_3877_);
                if v_isShared_3874_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3873_, 0);
                    crate::leanh::lean_ctor_set(v___x_3873_, 1, v___f_3884_);
                    crate::leanh::lean_ctor_set(v___x_3873_, 0, v___f_3883_);
                    v___x_3886_ = v___x_3873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___f_3883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___f_3884_);
                    v___x_3886_ = v_reuseFailAlloc_3931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_toSeqRight_3880_);
                v___f_3887_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3887_, 0, v_toSeqRight_3880_);
                crate::leanh::lean_inc(v_toSeqLeft_3879_);
                v___f_3888_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3888_, 0, v_toSeqLeft_3879_);
                crate::leanh::lean_inc(v_toSeq_3878_);
                v___f_3889_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3889_, 0, v_toSeq_3878_);
                v___x_3890_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3890_, 0, v___x_3886_);
                crate::leanh::lean_ctor_set(v___x_3890_, 1, v___f_3881_);
                crate::leanh::lean_ctor_set(v___x_3890_, 2, v___f_3889_);
                crate::leanh::lean_ctor_set(v___x_3890_, 3, v___f_3888_);
                crate::leanh::lean_ctor_set(v___x_3890_, 4, v___f_3887_);
                v___x_3891_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3891_, 0, v___x_3890_);
                crate::leanh::lean_ctor_set(v___x_3891_, 1, v___f_3882_);
                v___x_3892_ = l_StateRefT_x27_instMonad___redArg(v___x_3891_);
                v_toApplicative_3893_ = crate::leanh::lean_ctor_get(v___x_3892_, 0);
                v_isSharedCheck_3929_ = (!crate::leanh::lean_is_exclusive(v___x_3892_)) as u8;
                if v_isSharedCheck_3929_ == 0 {
                    v_unused_3930_ = crate::leanh::lean_ctor_get(v___x_3892_, 1);
                    crate::leanh::lean_dec(v_unused_3930_);
                    v___x_3895_ = v___x_3892_;
                    v_isShared_3896_ = v_isSharedCheck_3929_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3893_);
                    crate::leanh::lean_dec(v___x_3892_);
                    v___x_3895_ = crate::leanh::lean_box(0);
                    v_isShared_3896_ = v_isSharedCheck_3929_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_toFunctor_3897_ = crate::leanh::lean_ctor_get(v_toApplicative_3893_, 0);
                v_toSeq_3898_ = crate::leanh::lean_ctor_get(v_toApplicative_3893_, 2);
                v_toSeqLeft_3899_ = crate::leanh::lean_ctor_get(v_toApplicative_3893_, 3);
                v_toSeqRight_3900_ = crate::leanh::lean_ctor_get(v_toApplicative_3893_, 4);
                v_isSharedCheck_3927_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3893_)) as u8;
                if v_isSharedCheck_3927_ == 0 {
                    v_unused_3928_ = crate::leanh::lean_ctor_get(v_toApplicative_3893_, 1);
                    crate::leanh::lean_dec(v_unused_3928_);
                    v___x_3902_ = v_toApplicative_3893_;
                    v_isShared_3903_ = v_isSharedCheck_3927_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3900_);
                    crate::leanh::lean_inc(v_toSeqLeft_3899_);
                    crate::leanh::lean_inc(v_toSeq_3898_);
                    crate::leanh::lean_inc(v_toFunctor_3897_);
                    crate::leanh::lean_dec(v_toApplicative_3893_);
                    v___x_3902_ = crate::leanh::lean_box(0);
                    v_isShared_3903_ = v_isSharedCheck_3927_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3904_ = crate::leanh::lean_box((v_nondep_3854_) as usize);
                crate::leanh::lean_inc(v_toBind_3851_);
                crate::leanh::lean_inc_ref(v_e_3870_);
                v___f_3905_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed as *mut core::ffi::c_void, 8, 7);
                crate::leanh::lean_closure_set(v___f_3905_, 0, v_toApplicative_3845_);
                crate::leanh::lean_closure_set(v___f_3905_, 1, v_e_3870_);
                crate::leanh::lean_closure_set(v___f_3905_, 2, v_xs_3853_);
                crate::leanh::lean_closure_set(v___f_3905_, 3, v_h_3871_);
                crate::leanh::lean_closure_set(v___f_3905_, 4, v___x_3904_);
                crate::leanh::lean_closure_set(v___f_3905_, 5, v_toBind_3851_);
                crate::leanh::lean_closure_set(v___f_3905_, 6, v___f_3855_);
                v_cls_3906_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8;
                v___f_3907_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9;
                v___f_3908_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10;
                crate::leanh::lean_inc_ref(v_toFunctor_3897_);
                v___f_3909_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3909_, 0, v_toFunctor_3897_);
                v___f_3910_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3910_, 0, v_toFunctor_3897_);
                v___x_3911_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3911_, 0, v___f_3909_);
                crate::leanh::lean_ctor_set(v___x_3911_, 1, v___f_3910_);
                v___f_3912_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3912_, 0, v_toSeqRight_3900_);
                v___f_3913_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3913_, 0, v_toSeqLeft_3899_);
                v___f_3914_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3914_, 0, v_toSeq_3898_);
                if v_isShared_3903_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3902_, 4, v___f_3912_);
                    crate::leanh::lean_ctor_set(v___x_3902_, 3, v___f_3913_);
                    crate::leanh::lean_ctor_set(v___x_3902_, 2, v___f_3914_);
                    crate::leanh::lean_ctor_set(v___x_3902_, 1, v___f_3907_);
                    crate::leanh::lean_ctor_set(v___x_3902_, 0, v___x_3911_);
                    v___x_3916_ = v___x_3902_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3926_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 1, v___f_3907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 2, v___f_3914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 3, v___f_3913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 4, v___f_3912_);
                    v___x_3916_ = v_reuseFailAlloc_3926_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3895_, 1, v___f_3908_);
                    crate::leanh::lean_ctor_set(v___x_3895_, 0, v___x_3916_);
                    v___x_3918_ = v___x_3895_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 1, v___f_3908_);
                    v___x_3918_ = v_reuseFailAlloc_3925_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3919_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11;
                v___x_3920_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12;
                v___x_3921_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
                v___f_3922_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed as *mut core::ffi::c_void, 13, 8);
                crate::leanh::lean_closure_set(v___f_3922_, 0, v_cls_3906_);
                crate::leanh::lean_closure_set(v___f_3922_, 1, v___x_3920_);
                crate::leanh::lean_closure_set(v___f_3922_, 2, v___f_3919_);
                crate::leanh::lean_closure_set(v___f_3922_, 3, v_declName_3856_);
                crate::leanh::lean_closure_set(v___f_3922_, 4, v_val_3857_);
                crate::leanh::lean_closure_set(v___f_3922_, 5, v_e_3870_);
                crate::leanh::lean_closure_set(v___f_3922_, 6, v___x_3918_);
                crate::leanh::lean_closure_set(v___f_3922_, 7, v___x_3921_);
                v___x_3923_ = crate::leanh::lean_apply_2(
                    v_inst_3858_,
                    crate::leanh::lean_box(0),
                    v___f_3922_,
                );
                v___x_3924_ = crate::leanh::lean_apply_4(
                    v_toBind_3851_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3923_,
                    v___f_3905_,
                );
                return v___x_3924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(
    mut v_toApplicative_3933_: *mut crate::leanh::LeanObject,
    mut v_level_3934_: *mut crate::leanh::LeanObject,
    mut v___x_3935_: *mut crate::leanh::LeanObject,
    mut v_type_3936_: *mut crate::leanh::LeanObject,
    mut v_value_3937_: *mut crate::leanh::LeanObject,
    mut v___x_3938_: *mut crate::leanh::LeanObject,
    mut v_toBind_3939_: *mut crate::leanh::LeanObject,
    mut v___f_3940_: *mut crate::leanh::LeanObject,
    mut v_xs_3941_: *mut crate::leanh::LeanObject,
    mut v_nondep_3942_: *mut crate::leanh::LeanObject,
    mut v___f_3943_: *mut crate::leanh::LeanObject,
    mut v_declName_3944_: *mut crate::leanh::LeanObject,
    mut v_val_3945_: *mut crate::leanh::LeanObject,
    mut v_inst_3946_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13106__boxed_3948_: u8 = 0;
    let mut v_nondep_13108__boxed_3949_: u8 = 0;
    let mut v_res_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13106__boxed_3948_ = (crate::leanh::lean_unbox(v___x_3938_) as u8);
    v_nondep_13108__boxed_3949_ = (crate::leanh::lean_unbox(v_nondep_3942_) as u8);
    v_res_3950_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(
            v_toApplicative_3933_,
            v_level_3934_,
            v___x_3935_,
            v_type_3936_,
            v_value_3937_,
            v___x_13106__boxed_3948_,
            v_toBind_3939_,
            v___f_3940_,
            v_xs_3941_,
            v_nondep_13108__boxed_3949_,
            v___f_3943_,
            v_declName_3944_,
            v_val_3945_,
            v_inst_3946_,
            v_____do__lift_3947_,
        );
    return v_res_3950_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3960_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5;
    v___x_3961_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_3962_ = crate::leanh::lean_unsigned_to_nat(287);
    v___x_3963_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4;
    v___x_3964_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3;
    v___x_3965_ = l_mkPanicMessageWithDecl(
        v___x_3964_,
        v___x_3963_,
        v___x_3962_,
        v___x_3961_,
        v___x_3960_,
    );
    return v___x_3965_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(
    mut v_declName_3966_: *mut crate::leanh::LeanObject,
    mut v_type_3967_: *mut crate::leanh::LeanObject,
    mut v_fst_3968_: *mut crate::leanh::LeanObject,
    mut v___x_3969_: *mut crate::leanh::LeanObject,
    mut v_value_3970_: *mut crate::leanh::LeanObject,
    mut v_nondep_3971_: u8,
    mut v_fst_3972_: u8,
    mut v_toApplicative_3973_: *mut crate::leanh::LeanObject,
    mut v___x_3974_: *mut crate::leanh::LeanObject,
    mut v_us_3975_: *mut crate::leanh::LeanObject,
    mut v_snd_3976_: *mut crate::leanh::LeanObject,
    mut v_inst_3977_: *mut crate::leanh::LeanObject,
    mut v_rb_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expr_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprType_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprInit_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprResult_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_3984_: u8 = 0;
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3987_: u8 = 0;
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: u8 = 0;
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprType_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprInit_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprResult_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_expr_3979_ = crate::leanh::lean_ctor_get(v_rb_3978_, 0);
                v_exprType_3980_ = crate::leanh::lean_ctor_get(v_rb_3978_, 1);
                v_exprInit_3981_ = crate::leanh::lean_ctor_get(v_rb_3978_, 2);
                v_exprResult_3982_ = crate::leanh::lean_ctor_get(v_rb_3978_, 3);
                v_proof_3983_ = crate::leanh::lean_ctor_get(v_rb_3978_, 4);
                v_modified_3984_ = crate::leanh::lean_ctor_get_uint8(
                    v_rb_3978_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                );
                v_isSharedCheck_4035_ = (!crate::leanh::lean_is_exclusive(v_rb_3978_)) as u8;
                if v_isSharedCheck_4035_ == 0 {
                    v___x_3986_ = v_rb_3978_;
                    v_isShared_3987_ = v_isSharedCheck_4035_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_3983_);
                    crate::leanh::lean_inc(v_exprResult_3982_);
                    crate::leanh::lean_inc(v_exprInit_3981_);
                    crate::leanh::lean_inc(v_exprType_3980_);
                    crate::leanh::lean_inc(v_expr_3979_);
                    crate::leanh::lean_dec(v_rb_3978_);
                    v___x_3986_ = crate::leanh::lean_box(0);
                    v_isShared_3987_ = v_isSharedCheck_4035_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3988_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3989_ = lean_expr_has_loose_bvar(v_exprType_3980_, v___x_3988_);
                if v___x_3989_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_3977_);
                    v___x_3990_ = 0;
                    crate::leanh::lean_inc_ref_n(v_type_3967_, 3);
                    crate::leanh::lean_inc_n(v_declName_3966_, 3);
                    v___x_3991_ =
                        l_Lean_mkLambda(v_declName_3966_, v___x_3990_, v_type_3967_, v_expr_3979_);
                    crate::leanh::lean_inc_ref_n(v_fst_3968_, 2);
                    crate::leanh::lean_inc_ref(v___x_3991_);
                    v_expr_3992_ = l_Lean_Expr_app___override(v___x_3991_, v_fst_3968_);
                    v_exprType_3993_ =
                        lean_expr_lower_loose_bvars(v_exprType_3980_, v___x_3969_, v___x_3969_);
                    crate::leanh::lean_dec_ref(v_exprType_3980_);
                    v___x_3994_ = l_Lean_mkLambda(
                        v_declName_3966_,
                        v___x_3990_,
                        v_type_3967_,
                        v_exprInit_3981_,
                    );
                    crate::leanh::lean_inc_ref(v_value_3970_);
                    crate::leanh::lean_inc_ref(v___x_3994_);
                    v_exprInit_3995_ = l_Lean_Expr_app___override(v___x_3994_, v_value_3970_);
                    v_exprResult_3996_ = l_Lean_Expr_letE___override(
                        v_declName_3966_,
                        v_type_3967_,
                        v_fst_3968_,
                        v_exprResult_3982_,
                        v_nondep_3971_,
                    );
                    if v_fst_3972_ == 0 {
                        crate::leanh::lean_dec_ref(v_snd_3976_);
                        crate::leanh::lean_dec_ref(v_fst_3968_);
                        if v_modified_3984_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3994_);
                            crate::leanh::lean_dec_ref(v___x_3991_);
                            crate::leanh::lean_dec_ref(v_proof_3983_);
                            crate::leanh::lean_dec(v_us_3975_);
                            crate::leanh::lean_dec_ref(v_value_3970_);
                            crate::leanh::lean_dec_ref(v_type_3967_);
                            crate::leanh::lean_dec(v_declName_3966_);
                            v_toPure_3997_ = crate::leanh::lean_ctor_get(v_toApplicative_3973_, 1);
                            crate::leanh::lean_inc(v_toPure_3997_);
                            crate::leanh::lean_dec_ref(v_toApplicative_3973_);
                            v___x_3998_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2;
                            v___x_3999_ = l_Lean_mkConst(v___x_3998_, v___x_3974_);
                            crate::leanh::lean_inc_ref(v_expr_3992_);
                            crate::leanh::lean_inc_ref(v_exprType_3993_);
                            v_proof_4000_ =
                                l_Lean_mkAppB(v___x_3999_, v_exprType_3993_, v_expr_3992_);
                            if v_isShared_3987_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3986_, 4, v_proof_4000_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 3, v_exprResult_3996_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 2, v_exprInit_3995_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 1, v_exprType_3993_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 0, v_expr_3992_);
                                v___x_4002_ = v___x_3986_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_4004_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4004_,
                                    0,
                                    v_expr_3992_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4004_,
                                    1,
                                    v_exprType_3993_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4004_,
                                    2,
                                    v_exprInit_3995_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4004_,
                                    3,
                                    v_exprResult_3996_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4004_,
                                    4,
                                    v_proof_4000_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4004_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5)
                                        as u32,
                                    v_modified_3984_,
                                );
                                v___x_4002_ = v_reuseFailAlloc_4004_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3974_);
                            v_toPure_4005_ = crate::leanh::lean_ctor_get(v_toApplicative_3973_, 1);
                            crate::leanh::lean_inc(v_toPure_4005_);
                            crate::leanh::lean_dec_ref(v_toApplicative_3973_);
                            crate::leanh::lean_inc_ref(v_type_3967_);
                            v___x_4006_ = l_Lean_mkLambda(
                                v_declName_3966_,
                                v___x_3990_,
                                v_type_3967_,
                                v_proof_3983_,
                            );
                            v___x_4007_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0;
                            v___x_4008_ = l_Lean_mkConst(v___x_4007_, v_us_3975_);
                            crate::leanh::lean_inc_ref(v_exprType_3993_);
                            v_proof_4009_ = l_Lean_mkApp6(
                                v___x_4008_,
                                v_type_3967_,
                                v_exprType_3993_,
                                v_value_3970_,
                                v___x_3994_,
                                v___x_3991_,
                                v___x_4006_,
                            );
                            if v_isShared_3987_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3986_, 4, v_proof_4009_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 3, v_exprResult_3996_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 2, v_exprInit_3995_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 1, v_exprType_3993_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 0, v_expr_3992_);
                                v___x_4011_ = v___x_3986_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4013_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4013_,
                                    0,
                                    v_expr_3992_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4013_,
                                    1,
                                    v_exprType_3993_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4013_,
                                    2,
                                    v_exprInit_3995_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4013_,
                                    3,
                                    v_exprResult_3996_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4013_,
                                    4,
                                    v_proof_4009_,
                                );
                                v___x_4011_ = v_reuseFailAlloc_4013_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3974_);
                        if v_modified_3984_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3991_);
                            crate::leanh::lean_dec_ref(v_proof_3983_);
                            crate::leanh::lean_dec(v_declName_3966_);
                            v_toPure_4014_ = crate::leanh::lean_ctor_get(v_toApplicative_3973_, 1);
                            crate::leanh::lean_inc(v_toPure_4014_);
                            crate::leanh::lean_dec_ref(v_toApplicative_3973_);
                            v___x_4015_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1;
                            v___x_4016_ = l_Lean_mkConst(v___x_4015_, v_us_3975_);
                            crate::leanh::lean_inc_ref(v_exprType_3993_);
                            v_proof_4017_ = l_Lean_mkApp6(
                                v___x_4016_,
                                v_type_3967_,
                                v_exprType_3993_,
                                v_value_3970_,
                                v_fst_3968_,
                                v___x_3994_,
                                v_snd_3976_,
                            );
                            if v_isShared_3987_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3986_, 4, v_proof_4017_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 3, v_exprResult_3996_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 2, v_exprInit_3995_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 1, v_exprType_3993_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 0, v_expr_3992_);
                                v___x_4019_ = v___x_3986_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_4021_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4021_,
                                    0,
                                    v_expr_3992_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4021_,
                                    1,
                                    v_exprType_3993_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4021_,
                                    2,
                                    v_exprInit_3995_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4021_,
                                    3,
                                    v_exprResult_3996_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4021_,
                                    4,
                                    v_proof_4017_,
                                );
                                v___x_4019_ = v_reuseFailAlloc_4021_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_toPure_4022_ = crate::leanh::lean_ctor_get(v_toApplicative_3973_, 1);
                            crate::leanh::lean_inc(v_toPure_4022_);
                            crate::leanh::lean_dec_ref(v_toApplicative_3973_);
                            crate::leanh::lean_inc_ref(v_type_3967_);
                            v___x_4023_ = l_Lean_mkLambda(
                                v_declName_3966_,
                                v___x_3990_,
                                v_type_3967_,
                                v_proof_3983_,
                            );
                            v___x_4024_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2;
                            v___x_4025_ = l_Lean_mkConst(v___x_4024_, v_us_3975_);
                            crate::leanh::lean_inc_ref(v_exprType_3993_);
                            v_proof_4026_ = l_Lean_mkApp8(
                                v___x_4025_,
                                v_type_3967_,
                                v_exprType_3993_,
                                v_value_3970_,
                                v_fst_3968_,
                                v___x_3994_,
                                v___x_3991_,
                                v_snd_3976_,
                                v___x_4023_,
                            );
                            if v_isShared_3987_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3986_, 4, v_proof_4026_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 3, v_exprResult_3996_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 2, v_exprInit_3995_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 1, v_exprType_3993_);
                                crate::leanh::lean_ctor_set(v___x_3986_, 0, v_expr_3992_);
                                v___x_4028_ = v___x_3986_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_4030_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4030_,
                                    0,
                                    v_expr_3992_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4030_,
                                    1,
                                    v_exprType_3993_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4030_,
                                    2,
                                    v_exprInit_3995_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4030_,
                                    3,
                                    v_exprResult_3996_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4030_,
                                    4,
                                    v_proof_4026_,
                                );
                                v___x_4028_ = v_reuseFailAlloc_4030_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3986_);
                    crate::leanh::lean_dec_ref(v_proof_3983_);
                    crate::leanh::lean_dec_ref(v_exprResult_3982_);
                    crate::leanh::lean_dec_ref(v_exprInit_3981_);
                    crate::leanh::lean_dec_ref(v_exprType_3980_);
                    crate::leanh::lean_dec_ref(v_expr_3979_);
                    crate::leanh::lean_dec_ref(v_snd_3976_);
                    crate::leanh::lean_dec(v_us_3975_);
                    crate::leanh::lean_dec(v___x_3974_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3973_);
                    crate::leanh::lean_dec_ref(v_value_3970_);
                    crate::leanh::lean_dec_ref(v_fst_3968_);
                    crate::leanh::lean_dec_ref(v_type_3967_);
                    crate::leanh::lean_dec(v_declName_3966_);
                    v___x_4031_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
                    v___x_4032_ = l_instInhabitedOfMonad___redArg(v_inst_3977_, v___x_4031_);
                    v___x_4033_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
                    v___x_4034_ = l_panic___redArg(v___x_4032_, v___x_4033_);
                    crate::leanh::lean_dec(v___x_4032_);
                    return v___x_4034_;
                }
            }
            2 => {
                v___x_4003_ = crate::leanh::lean_apply_2(
                    v_toPure_3997_,
                    crate::leanh::lean_box(0),
                    v___x_4002_,
                );
                return v___x_4003_;
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4011_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_nondep_3971_,
                );
                v___x_4012_ = crate::leanh::lean_apply_2(
                    v_toPure_4005_,
                    crate::leanh::lean_box(0),
                    v___x_4011_,
                );
                return v___x_4012_;
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4019_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_nondep_3971_,
                );
                v___x_4020_ = crate::leanh::lean_apply_2(
                    v_toPure_4014_,
                    crate::leanh::lean_box(0),
                    v___x_4019_,
                );
                return v___x_4020_;
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4028_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_nondep_3971_,
                );
                v___x_4029_ = crate::leanh::lean_apply_2(
                    v_toPure_4022_,
                    crate::leanh::lean_box(0),
                    v___x_4028_,
                );
                return v___x_4029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(
    mut v_declName_4036_: *mut crate::leanh::LeanObject,
    mut v_type_4037_: *mut crate::leanh::LeanObject,
    mut v_fst_4038_: *mut crate::leanh::LeanObject,
    mut v___x_4039_: *mut crate::leanh::LeanObject,
    mut v_value_4040_: *mut crate::leanh::LeanObject,
    mut v_nondep_4041_: *mut crate::leanh::LeanObject,
    mut v_fst_4042_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_4043_: *mut crate::leanh::LeanObject,
    mut v___x_4044_: *mut crate::leanh::LeanObject,
    mut v_us_4045_: *mut crate::leanh::LeanObject,
    mut v_snd_4046_: *mut crate::leanh::LeanObject,
    mut v_inst_4047_: *mut crate::leanh::LeanObject,
    mut v_rb_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_13324__boxed_4049_: u8 = 0;
    let mut v_fst_13325__boxed_4050_: u8 = 0;
    let mut v_res_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_13324__boxed_4049_ = (crate::leanh::lean_unbox(v_nondep_4041_) as u8);
    v_fst_13325__boxed_4050_ = (crate::leanh::lean_unbox(v_fst_4042_) as u8);
    v_res_4051_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(
            v_declName_4036_,
            v_type_4037_,
            v_fst_4038_,
            v___x_4039_,
            v_value_4040_,
            v_nondep_13324__boxed_4049_,
            v_fst_13325__boxed_4050_,
            v_toApplicative_4043_,
            v___x_4044_,
            v_us_4045_,
            v_snd_4046_,
            v_inst_4047_,
            v_rb_4048_,
        );
    crate::leanh::lean_dec(v___x_4039_);
    return v_res_4051_;
}
pub unsafe fn _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0;
    v___x_4057_ = crate::leanh::lean_unsigned_to_nat(34);
    v___x_4058_ = crate::leanh::lean_unsigned_to_nat(217);
    v___x_4059_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4;
    v___x_4060_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3;
    v___x_4061_ = l_mkPanicMessageWithDecl(
        v___x_4060_,
        v___x_4059_,
        v___x_4058_,
        v___x_4057_,
        v___x_4056_,
    );
    return v___x_4061_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(
    mut v_declName_4062_: *mut crate::leanh::LeanObject,
    mut v_type_4063_: *mut crate::leanh::LeanObject,
    mut v_value_4064_: *mut crate::leanh::LeanObject,
    mut v_nondep_4065_: u8,
    mut v_toApplicative_4066_: *mut crate::leanh::LeanObject,
    mut v___x_4067_: *mut crate::leanh::LeanObject,
    mut v_us_4068_: *mut crate::leanh::LeanObject,
    mut v_decl_4069_: *mut crate::leanh::LeanObject,
    mut v_x_4070_: *mut crate::leanh::LeanObject,
    mut v_i_4071_: *mut crate::leanh::LeanObject,
    mut v_xs_4072_: *mut crate::leanh::LeanObject,
    mut v_inst_4073_: *mut crate::leanh::LeanObject,
    mut v_inst_4074_: *mut crate::leanh::LeanObject,
    mut v_inst_4075_: *mut crate::leanh::LeanObject,
    mut v_inst_4076_: *mut crate::leanh::LeanObject,
    mut v_info_4077_: *mut crate::leanh::LeanObject,
    mut v_fixed_4078_: *mut crate::leanh::LeanObject,
    mut v_used_4079_: *mut crate::leanh::LeanObject,
    mut v_body_4080_: *mut crate::leanh::LeanObject,
    mut v_toBind_4081_: *mut crate::leanh::LeanObject,
    mut v_withNewLemmas_4082_: *mut crate::leanh::LeanObject,
    mut v_val_x27_4083_: *mut crate::leanh::LeanObject,
    mut v_val_4084_: *mut crate::leanh::LeanObject,
    mut v___x_4085_: u8,
    mut v_____r_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4088_: u8 = 0;
    let mut v___y_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4105_: u8 = 0;
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4107_ = lean_expr_eqv(v_val_4084_, v_val_x27_4083_);
                if v___x_4107_ == 0 {
                    v___y_4105_ = v_nondep_4065_;
                    state = 2;
                    continue;
                } else {
                    v___y_4105_ = v___x_4085_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4090_ = crate::leanh::lean_box((v_nondep_4065_) as usize);
                v___x_4091_ = crate::leanh::lean_box((v___y_4088_) as usize);
                v___f_4092_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed as *mut core::ffi::c_void, 10, 9);
                crate::leanh::lean_closure_set(v___f_4092_, 0, v_declName_4062_);
                crate::leanh::lean_closure_set(v___f_4092_, 1, v_type_4063_);
                crate::leanh::lean_closure_set(v___f_4092_, 2, v___y_4089_);
                crate::leanh::lean_closure_set(v___f_4092_, 3, v_value_4064_);
                crate::leanh::lean_closure_set(v___f_4092_, 4, v___x_4090_);
                crate::leanh::lean_closure_set(v___f_4092_, 5, v_toApplicative_4066_);
                crate::leanh::lean_closure_set(v___f_4092_, 6, v___x_4067_);
                crate::leanh::lean_closure_set(v___f_4092_, 7, v___x_4091_);
                crate::leanh::lean_closure_set(v___f_4092_, 8, v_us_4068_);
                v___x_4093_ = crate::leanh::lean_box(0);
                v___x_4094_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4094_, 0, v_decl_4069_);
                crate::leanh::lean_ctor_set(v___x_4094_, 1, v___x_4093_);
                v___x_4095_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4096_ = lean_mk_empty_array_with_capacity(v___x_4095_);
                crate::leanh::lean_inc_ref(v_x_4070_);
                v___x_4097_ = lean_array_push(v___x_4096_, v_x_4070_);
                v___x_4098_ = lean_nat_add(v_i_4071_, v___x_4095_);
                v___x_4099_ = lean_array_push(v_xs_4072_, v_x_4070_);
                crate::leanh::lean_inc_ref(v_inst_4075_);
                crate::leanh::lean_inc_ref(v_inst_4073_);
                v___x_4100_ =
                    l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(
                        v_inst_4073_,
                        v_inst_4074_,
                        v_inst_4075_,
                        v_inst_4076_,
                        v_info_4077_,
                        v_fixed_4078_,
                        v_used_4079_,
                        v_body_4080_,
                        v___x_4098_,
                        v___x_4099_,
                    );
                v___x_4101_ = crate::leanh::lean_apply_4(
                    v_toBind_4081_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4100_,
                    v___f_4092_,
                );
                v___x_4102_ = crate::leanh::lean_apply_3(
                    v_withNewLemmas_4082_,
                    crate::leanh::lean_box(0),
                    v___x_4097_,
                    v___x_4101_,
                );
                v___x_4103_ = l_Lean_Meta_withExistingLocalDecls___redArg(
                    v_inst_4075_,
                    v_inst_4073_,
                    v___x_4094_,
                    v___x_4102_,
                );
                return v___x_4103_;
            }
            2 => {
                if v___y_4105_ == 0 {
                    crate::leanh::lean_inc_ref(v_value_4064_);
                    v___y_4088_ = v___y_4105_;
                    v___y_4089_ = v_value_4064_;
                    state = 1;
                    continue;
                } else {
                    v___x_4106_ = lean_expr_abstract(v_val_x27_4083_, v_xs_4072_);
                    v___y_4088_ = v___y_4105_;
                    v___y_4089_ = v___x_4106_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_4108_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_type_4109_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_value_4110_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_nondep_4111_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_toApplicative_4112_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_4113_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_us_4114_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_decl_4115_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_x_4116_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_i_4117_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_xs_4118_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_4119_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_4120_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_4121_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_4122_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_info_4123_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_fixed_4124_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_used_4125_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_body_4126_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_toBind_4127_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_withNewLemmas_4128_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_val_x27_4129_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_val_4130_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___x_4131_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v_____r_4132_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_nondep_13580__boxed_4133_: u8 = 0;
    let mut v___x_13587__boxed_4134_: u8 = 0;
    let mut v_res_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_13580__boxed_4133_ = (crate::leanh::lean_unbox(v_nondep_4111_) as u8);
    v___x_13587__boxed_4134_ = (crate::leanh::lean_unbox(v___x_4131_) as u8);
    v_res_4135_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(
            v_declName_4108_,
            v_type_4109_,
            v_value_4110_,
            v_nondep_13580__boxed_4133_,
            v_toApplicative_4112_,
            v___x_4113_,
            v_us_4114_,
            v_decl_4115_,
            v_x_4116_,
            v_i_4117_,
            v_xs_4118_,
            v_inst_4119_,
            v_inst_4120_,
            v_inst_4121_,
            v_inst_4122_,
            v_info_4123_,
            v_fixed_4124_,
            v_used_4125_,
            v_body_4126_,
            v_toBind_4127_,
            v_withNewLemmas_4128_,
            v_val_x27_4129_,
            v_val_4130_,
            v___x_13587__boxed_4134_,
            v_____r_4132_,
        );
    crate::leanh::lean_dec_ref(v_val_4130_);
    crate::leanh::lean_dec_ref(v_val_x27_4129_);
    crate::leanh::lean_dec(v_i_4117_);
    return v_res_4135_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(
    mut v_declName_4136_: *mut crate::leanh::LeanObject,
    mut v_type_4137_: *mut crate::leanh::LeanObject,
    mut v_value_4138_: *mut crate::leanh::LeanObject,
    mut v_nondep_4139_: u8,
    mut v_toApplicative_4140_: *mut crate::leanh::LeanObject,
    mut v___x_4141_: *mut crate::leanh::LeanObject,
    mut v_us_4142_: *mut crate::leanh::LeanObject,
    mut v_decl_4143_: *mut crate::leanh::LeanObject,
    mut v_x_4144_: *mut crate::leanh::LeanObject,
    mut v_i_4145_: *mut crate::leanh::LeanObject,
    mut v_xs_4146_: *mut crate::leanh::LeanObject,
    mut v_inst_4147_: *mut crate::leanh::LeanObject,
    mut v_inst_4148_: *mut crate::leanh::LeanObject,
    mut v_inst_4149_: *mut crate::leanh::LeanObject,
    mut v_inst_4150_: *mut crate::leanh::LeanObject,
    mut v_info_4151_: *mut crate::leanh::LeanObject,
    mut v_fixed_4152_: *mut crate::leanh::LeanObject,
    mut v_used_4153_: *mut crate::leanh::LeanObject,
    mut v_body_4154_: *mut crate::leanh::LeanObject,
    mut v_toBind_4155_: *mut crate::leanh::LeanObject,
    mut v_withNewLemmas_4156_: *mut crate::leanh::LeanObject,
    mut v_val_4157_: *mut crate::leanh::LeanObject,
    mut v___x_4158_: u8,
    mut v_val_x27_4159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v_toFunctor_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_unused_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4214_: u8 = 0;
    let mut v_unused_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4160_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
                v_toApplicative_4161_ = crate::leanh::lean_ctor_get(v___x_4160_, 0);
                v_toFunctor_4162_ = crate::leanh::lean_ctor_get(v_toApplicative_4161_, 0);
                v_toSeq_4163_ = crate::leanh::lean_ctor_get(v_toApplicative_4161_, 2);
                v_toSeqLeft_4164_ = crate::leanh::lean_ctor_get(v_toApplicative_4161_, 3);
                v_toSeqRight_4165_ = crate::leanh::lean_ctor_get(v_toApplicative_4161_, 4);
                v___f_4166_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2;
                v___f_4167_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_4162_, 2);
                v___f_4168_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4168_, 0, v_toFunctor_4162_);
                v___f_4169_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4169_, 0, v_toFunctor_4162_);
                v___x_4170_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4170_, 0, v___f_4168_);
                crate::leanh::lean_ctor_set(v___x_4170_, 1, v___f_4169_);
                crate::leanh::lean_inc(v_toSeqRight_4165_);
                v___f_4171_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4171_, 0, v_toSeqRight_4165_);
                crate::leanh::lean_inc(v_toSeqLeft_4164_);
                v___f_4172_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4172_, 0, v_toSeqLeft_4164_);
                crate::leanh::lean_inc(v_toSeq_4163_);
                v___f_4173_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4173_, 0, v_toSeq_4163_);
                v___x_4174_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4174_, 0, v___x_4170_);
                crate::leanh::lean_ctor_set(v___x_4174_, 1, v___f_4166_);
                crate::leanh::lean_ctor_set(v___x_4174_, 2, v___f_4173_);
                crate::leanh::lean_ctor_set(v___x_4174_, 3, v___f_4172_);
                crate::leanh::lean_ctor_set(v___x_4174_, 4, v___f_4171_);
                v___x_4175_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4175_, 0, v___x_4174_);
                crate::leanh::lean_ctor_set(v___x_4175_, 1, v___f_4167_);
                v___x_4176_ = l_StateRefT_x27_instMonad___redArg(v___x_4175_);
                v_toApplicative_4177_ = crate::leanh::lean_ctor_get(v___x_4176_, 0);
                v_isSharedCheck_4214_ = (!crate::leanh::lean_is_exclusive(v___x_4176_)) as u8;
                if v_isSharedCheck_4214_ == 0 {
                    v_unused_4215_ = crate::leanh::lean_ctor_get(v___x_4176_, 1);
                    crate::leanh::lean_dec(v_unused_4215_);
                    v___x_4179_ = v___x_4176_;
                    v_isShared_4180_ = v_isSharedCheck_4214_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4177_);
                    crate::leanh::lean_dec(v___x_4176_);
                    v___x_4179_ = crate::leanh::lean_box(0);
                    v_isShared_4180_ = v_isSharedCheck_4214_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4181_ = crate::leanh::lean_ctor_get(v_toApplicative_4177_, 0);
                v_toSeq_4182_ = crate::leanh::lean_ctor_get(v_toApplicative_4177_, 2);
                v_toSeqLeft_4183_ = crate::leanh::lean_ctor_get(v_toApplicative_4177_, 3);
                v_toSeqRight_4184_ = crate::leanh::lean_ctor_get(v_toApplicative_4177_, 4);
                v_isSharedCheck_4212_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4177_)) as u8;
                if v_isSharedCheck_4212_ == 0 {
                    v_unused_4213_ = crate::leanh::lean_ctor_get(v_toApplicative_4177_, 1);
                    crate::leanh::lean_dec(v_unused_4213_);
                    v___x_4186_ = v_toApplicative_4177_;
                    v_isShared_4187_ = v_isSharedCheck_4212_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4184_);
                    crate::leanh::lean_inc(v_toSeqLeft_4183_);
                    crate::leanh::lean_inc(v_toSeq_4182_);
                    crate::leanh::lean_inc(v_toFunctor_4181_);
                    crate::leanh::lean_dec(v_toApplicative_4177_);
                    v___x_4186_ = crate::leanh::lean_box(0);
                    v_isShared_4187_ = v_isSharedCheck_4212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4188_ = crate::leanh::lean_box((v_nondep_4139_) as usize);
                v___x_4189_ = crate::leanh::lean_box((v___x_4158_) as usize);
                crate::leanh::lean_inc_ref(v_val_4157_);
                crate::leanh::lean_inc_ref(v_val_x27_4159_);
                crate::leanh::lean_inc(v_toBind_4155_);
                crate::leanh::lean_inc(v_inst_4148_);
                crate::leanh::lean_inc(v_declName_4136_);
                v___f_4190_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed as *mut core::ffi::c_void, 25, 24);
                crate::leanh::lean_closure_set(v___f_4190_, 0, v_declName_4136_);
                crate::leanh::lean_closure_set(v___f_4190_, 1, v_type_4137_);
                crate::leanh::lean_closure_set(v___f_4190_, 2, v_value_4138_);
                crate::leanh::lean_closure_set(v___f_4190_, 3, v___x_4188_);
                crate::leanh::lean_closure_set(v___f_4190_, 4, v_toApplicative_4140_);
                crate::leanh::lean_closure_set(v___f_4190_, 5, v___x_4141_);
                crate::leanh::lean_closure_set(v___f_4190_, 6, v_us_4142_);
                crate::leanh::lean_closure_set(v___f_4190_, 7, v_decl_4143_);
                crate::leanh::lean_closure_set(v___f_4190_, 8, v_x_4144_);
                crate::leanh::lean_closure_set(v___f_4190_, 9, v_i_4145_);
                crate::leanh::lean_closure_set(v___f_4190_, 10, v_xs_4146_);
                crate::leanh::lean_closure_set(v___f_4190_, 11, v_inst_4147_);
                crate::leanh::lean_closure_set(v___f_4190_, 12, v_inst_4148_);
                crate::leanh::lean_closure_set(v___f_4190_, 13, v_inst_4149_);
                crate::leanh::lean_closure_set(v___f_4190_, 14, v_inst_4150_);
                crate::leanh::lean_closure_set(v___f_4190_, 15, v_info_4151_);
                crate::leanh::lean_closure_set(v___f_4190_, 16, v_fixed_4152_);
                crate::leanh::lean_closure_set(v___f_4190_, 17, v_used_4153_);
                crate::leanh::lean_closure_set(v___f_4190_, 18, v_body_4154_);
                crate::leanh::lean_closure_set(v___f_4190_, 19, v_toBind_4155_);
                crate::leanh::lean_closure_set(v___f_4190_, 20, v_withNewLemmas_4156_);
                crate::leanh::lean_closure_set(v___f_4190_, 21, v_val_x27_4159_);
                crate::leanh::lean_closure_set(v___f_4190_, 22, v_val_4157_);
                crate::leanh::lean_closure_set(v___f_4190_, 23, v___x_4189_);
                v_cls_4191_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8;
                v___f_4192_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9;
                v___f_4193_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10;
                crate::leanh::lean_inc_ref(v_toFunctor_4181_);
                v___f_4194_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4194_, 0, v_toFunctor_4181_);
                v___f_4195_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4195_, 0, v_toFunctor_4181_);
                v___x_4196_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4196_, 0, v___f_4194_);
                crate::leanh::lean_ctor_set(v___x_4196_, 1, v___f_4195_);
                v___f_4197_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4197_, 0, v_toSeqRight_4184_);
                v___f_4198_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4198_, 0, v_toSeqLeft_4183_);
                v___f_4199_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4199_, 0, v_toSeq_4182_);
                if v_isShared_4187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4186_, 4, v___f_4197_);
                    crate::leanh::lean_ctor_set(v___x_4186_, 3, v___f_4198_);
                    crate::leanh::lean_ctor_set(v___x_4186_, 2, v___f_4199_);
                    crate::leanh::lean_ctor_set(v___x_4186_, 1, v___f_4192_);
                    crate::leanh::lean_ctor_set(v___x_4186_, 0, v___x_4196_);
                    v___x_4201_ = v___x_4186_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 1, v___f_4192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 2, v___f_4199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 3, v___f_4198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 4, v___f_4197_);
                    v___x_4201_ = v_reuseFailAlloc_4211_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4179_, 1, v___f_4193_);
                    crate::leanh::lean_ctor_set(v___x_4179_, 0, v___x_4201_);
                    v___x_4203_ = v___x_4179_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4210_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 1, v___f_4193_);
                    v___x_4203_ = v_reuseFailAlloc_4210_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___f_4204_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11;
                v___x_4205_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12;
                v___x_4206_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
                v___f_4207_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed as *mut core::ffi::c_void, 13, 8);
                crate::leanh::lean_closure_set(v___f_4207_, 0, v_cls_4191_);
                crate::leanh::lean_closure_set(v___f_4207_, 1, v___x_4205_);
                crate::leanh::lean_closure_set(v___f_4207_, 2, v___f_4204_);
                crate::leanh::lean_closure_set(v___f_4207_, 3, v_declName_4136_);
                crate::leanh::lean_closure_set(v___f_4207_, 4, v_val_4157_);
                crate::leanh::lean_closure_set(v___f_4207_, 5, v_val_x27_4159_);
                crate::leanh::lean_closure_set(v___f_4207_, 6, v___x_4203_);
                crate::leanh::lean_closure_set(v___f_4207_, 7, v___x_4206_);
                v___x_4208_ = crate::leanh::lean_apply_2(
                    v_inst_4148_,
                    crate::leanh::lean_box(0),
                    v___f_4207_,
                );
                v___x_4209_ = crate::leanh::lean_apply_4(
                    v_toBind_4155_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4208_,
                    v___f_4190_,
                );
                return v___x_4209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_4216_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_type_4217_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_value_4218_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_nondep_4219_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_toApplicative_4220_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_4221_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_us_4222_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_decl_4223_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_x_4224_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_i_4225_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_xs_4226_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_4227_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_4228_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_4229_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_4230_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_info_4231_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_fixed_4232_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_used_4233_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_body_4234_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_toBind_4235_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_withNewLemmas_4236_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_val_4237_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___x_4238_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_val_x27_4239_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v_nondep_13611__boxed_4240_: u8 = 0;
    let mut v___x_13618__boxed_4241_: u8 = 0;
    let mut v_res_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_13611__boxed_4240_ = (crate::leanh::lean_unbox(v_nondep_4219_) as u8);
    v___x_13618__boxed_4241_ = (crate::leanh::lean_unbox(v___x_4238_) as u8);
    v_res_4242_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(
            v_declName_4216_,
            v_type_4217_,
            v_value_4218_,
            v_nondep_13611__boxed_4240_,
            v_toApplicative_4220_,
            v___x_4221_,
            v_us_4222_,
            v_decl_4223_,
            v_x_4224_,
            v_i_4225_,
            v_xs_4226_,
            v_inst_4227_,
            v_inst_4228_,
            v_inst_4229_,
            v_inst_4230_,
            v_info_4231_,
            v_fixed_4232_,
            v_used_4233_,
            v_body_4234_,
            v_toBind_4235_,
            v_withNewLemmas_4236_,
            v_val_4237_,
            v___x_13618__boxed_4241_,
            v_val_x27_4239_,
        );
    return v_res_4242_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(
    mut v_decl_4243_: *mut crate::leanh::LeanObject,
    mut v_declName_4244_: *mut crate::leanh::LeanObject,
    mut v_type_4245_: *mut crate::leanh::LeanObject,
    mut v_value_4246_: *mut crate::leanh::LeanObject,
    mut v_nondep_4247_: u8,
    mut v_toApplicative_4248_: *mut crate::leanh::LeanObject,
    mut v___x_4249_: *mut crate::leanh::LeanObject,
    mut v_us_4250_: *mut crate::leanh::LeanObject,
    mut v_inst_4251_: *mut crate::leanh::LeanObject,
    mut v_x_4252_: *mut crate::leanh::LeanObject,
    mut v_i_4253_: *mut crate::leanh::LeanObject,
    mut v_xs_4254_: *mut crate::leanh::LeanObject,
    mut v_inst_4255_: *mut crate::leanh::LeanObject,
    mut v_inst_4256_: *mut crate::leanh::LeanObject,
    mut v_inst_4257_: *mut crate::leanh::LeanObject,
    mut v_info_4258_: *mut crate::leanh::LeanObject,
    mut v_fixed_4259_: *mut crate::leanh::LeanObject,
    mut v_used_4260_: *mut crate::leanh::LeanObject,
    mut v_body_4261_: *mut crate::leanh::LeanObject,
    mut v_toBind_4262_: *mut crate::leanh::LeanObject,
    mut v_withNewLemmas_4263_: *mut crate::leanh::LeanObject,
    mut v_____x_4264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4271_: u8 = 0;
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4265_ = crate::leanh::lean_ctor_get(v_____x_4264_, 1);
                crate::leanh::lean_inc(v_snd_4265_);
                v_fst_4266_ = crate::leanh::lean_ctor_get(v_____x_4264_, 0);
                crate::leanh::lean_inc(v_fst_4266_);
                crate::leanh::lean_dec_ref(v_____x_4264_);
                v_fst_4267_ = crate::leanh::lean_ctor_get(v_snd_4265_, 0);
                v_snd_4268_ = crate::leanh::lean_ctor_get(v_snd_4265_, 1);
                v_isSharedCheck_4287_ = (!crate::leanh::lean_is_exclusive(v_snd_4265_)) as u8;
                if v_isSharedCheck_4287_ == 0 {
                    v___x_4270_ = v_snd_4265_;
                    v_isShared_4271_ = v_isSharedCheck_4287_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4268_);
                    crate::leanh::lean_inc(v_fst_4267_);
                    crate::leanh::lean_dec(v_snd_4265_);
                    v___x_4270_ = crate::leanh::lean_box(0);
                    v_isShared_4271_ = v_isSharedCheck_4287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4272_ = crate::leanh::lean_box(0);
                if v_isShared_4271_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4270_, 1);
                    crate::leanh::lean_ctor_set(v___x_4270_, 1, v___x_4272_);
                    crate::leanh::lean_ctor_set(v___x_4270_, 0, v_decl_4243_);
                    v___x_4274_ = v___x_4270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4286_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_decl_4243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4286_, 1, v___x_4272_);
                    v___x_4274_ = v_reuseFailAlloc_4286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4275_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4276_ = crate::leanh::lean_box((v_nondep_4247_) as usize);
                crate::leanh::lean_inc_ref_n(v_inst_4251_, 2);
                v___f_4277_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed as *mut core::ffi::c_void, 13, 12);
                crate::leanh::lean_closure_set(v___f_4277_, 0, v_declName_4244_);
                crate::leanh::lean_closure_set(v___f_4277_, 1, v_type_4245_);
                crate::leanh::lean_closure_set(v___f_4277_, 2, v_fst_4266_);
                crate::leanh::lean_closure_set(v___f_4277_, 3, v___x_4275_);
                crate::leanh::lean_closure_set(v___f_4277_, 4, v_value_4246_);
                crate::leanh::lean_closure_set(v___f_4277_, 5, v___x_4276_);
                crate::leanh::lean_closure_set(v___f_4277_, 6, v_fst_4267_);
                crate::leanh::lean_closure_set(v___f_4277_, 7, v_toApplicative_4248_);
                crate::leanh::lean_closure_set(v___f_4277_, 8, v___x_4249_);
                crate::leanh::lean_closure_set(v___f_4277_, 9, v_us_4250_);
                crate::leanh::lean_closure_set(v___f_4277_, 10, v_snd_4268_);
                crate::leanh::lean_closure_set(v___f_4277_, 11, v_inst_4251_);
                v___x_4278_ = lean_mk_empty_array_with_capacity(v___x_4275_);
                crate::leanh::lean_inc_ref(v_x_4252_);
                v___x_4279_ = lean_array_push(v___x_4278_, v_x_4252_);
                v___x_4280_ = lean_nat_add(v_i_4253_, v___x_4275_);
                v___x_4281_ = lean_array_push(v_xs_4254_, v_x_4252_);
                crate::leanh::lean_inc_ref(v_inst_4256_);
                v___x_4282_ =
                    l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(
                        v_inst_4251_,
                        v_inst_4255_,
                        v_inst_4256_,
                        v_inst_4257_,
                        v_info_4258_,
                        v_fixed_4259_,
                        v_used_4260_,
                        v_body_4261_,
                        v___x_4280_,
                        v___x_4281_,
                    );
                v___x_4283_ = crate::leanh::lean_apply_4(
                    v_toBind_4262_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4282_,
                    v___f_4277_,
                );
                v___x_4284_ = crate::leanh::lean_apply_3(
                    v_withNewLemmas_4263_,
                    crate::leanh::lean_box(0),
                    v___x_4279_,
                    v___x_4283_,
                );
                v___x_4285_ = l_Lean_Meta_withExistingLocalDecls___redArg(
                    v_inst_4256_,
                    v_inst_4251_,
                    v___x_4274_,
                    v___x_4284_,
                );
                return v___x_4285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_4288_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_declName_4289_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_type_4290_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_value_4291_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_nondep_4292_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_toApplicative_4293_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_4294_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_us_4295_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_4296_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_x_4297_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_i_4298_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_xs_4299_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_4300_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_4301_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_4302_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_info_4303_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_fixed_4304_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_used_4305_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_body_4306_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_toBind_4307_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_withNewLemmas_4308_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_____x_4309_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_nondep_13553__boxed_4310_: u8 = 0;
    let mut v_res_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_13553__boxed_4310_ = (crate::leanh::lean_unbox(v_nondep_4292_) as u8);
    v_res_4311_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(
            v_decl_4288_,
            v_declName_4289_,
            v_type_4290_,
            v_value_4291_,
            v_nondep_13553__boxed_4310_,
            v_toApplicative_4293_,
            v___x_4294_,
            v_us_4295_,
            v_inst_4296_,
            v_x_4297_,
            v_i_4298_,
            v_xs_4299_,
            v_inst_4300_,
            v_inst_4301_,
            v_inst_4302_,
            v_info_4303_,
            v_fixed_4304_,
            v_used_4305_,
            v_body_4306_,
            v_toBind_4307_,
            v_withNewLemmas_4308_,
            v_____x_4309_,
        );
    crate::leanh::lean_dec(v_i_4298_);
    return v_res_4311_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4312_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_declName_4313_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_type_4314_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_value_4315_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_us_4316_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_4317_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_toApplicative_4318_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_nondep_4319_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_i_4320_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_xs_4321_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_4322_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_4323_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_4324_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_4325_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_info_4326_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_fixed_4327_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_used_4328_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_body_4329_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_toBind_4330_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_____r_4331_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_nondep_13536__boxed_4332_: u8 = 0;
    let mut v_res_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_13536__boxed_4332_ = (crate::leanh::lean_unbox(v_nondep_4319_) as u8);
    v_res_4333_ =
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(
            v___x_4312_,
            v_declName_4313_,
            v_type_4314_,
            v_value_4315_,
            v_us_4316_,
            v___x_4317_,
            v_toApplicative_4318_,
            v_nondep_13536__boxed_4332_,
            v_i_4320_,
            v_xs_4321_,
            v_inst_4322_,
            v_inst_4323_,
            v_inst_4324_,
            v_inst_4325_,
            v_info_4326_,
            v_fixed_4327_,
            v_used_4328_,
            v_body_4329_,
            v_toBind_4330_,
            v_____r_4331_,
        );
    crate::leanh::lean_dec(v_i_4320_);
    return v_res_4333_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(
    mut v_inst_4334_: *mut crate::leanh::LeanObject,
    mut v_inst_4335_: *mut crate::leanh::LeanObject,
    mut v_inst_4336_: *mut crate::leanh::LeanObject,
    mut v_inst_4337_: *mut crate::leanh::LeanObject,
    mut v_info_4338_: *mut crate::leanh::LeanObject,
    mut v_fixed_4339_: *mut crate::leanh::LeanObject,
    mut v_used_4340_: *mut crate::leanh::LeanObject,
    mut v_e_4341_: *mut crate::leanh::LeanObject,
    mut v_i_4342_: *mut crate::leanh::LeanObject,
    mut v_xs_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_haveInfo_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodyType_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_level_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: u8 = 0;
    let mut v_toApplicative_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4381_: u8 = 0;
    let mut v_toFunctor_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4388_: u8 = 0;
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut v_unused_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v_unused_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4417_: u8 = 0;
    let mut v_nondep_4418_: u8 = 0;
    let mut v_declName_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hinfo_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_level_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4432_: u8 = 0;
    let mut v_toApplicative_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_withNewLemmas_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dsimp_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: u8 = 0;
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: u8 = 0;
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v_toApplicative_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_withNewLemmas_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: u8 = 0;
    let mut v_toApplicative_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4485_: u8 = 0;
    let mut v_toFunctor_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4492_: u8 = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4516_: u8 = 0;
    let mut v_unused_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4518_: u8 = 0;
    let mut v_unused_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_haveInfo_4349_ = crate::leanh::lean_ctor_get(v_info_4338_, 0);
                v_body_4350_ = crate::leanh::lean_ctor_get(v_info_4338_, 3);
                v_bodyType_4351_ = crate::leanh::lean_ctor_get(v_info_4338_, 4);
                v_level_4352_ = crate::leanh::lean_ctor_get(v_info_4338_, 5);
                v___x_4353_ = lean_array_get_size(v_haveInfo_4349_);
                v___x_4354_ = lean_nat_dec_lt(v_i_4342_, v___x_4353_);
                if v___x_4354_ == 0 {
                    crate::leanh::lean_inc(v_level_4352_);
                    crate::leanh::lean_inc_ref(v_bodyType_4351_);
                    crate::leanh::lean_inc_ref(v_body_4350_);
                    crate::leanh::lean_dec(v_i_4342_);
                    crate::leanh::lean_dec_ref(v_used_4340_);
                    crate::leanh::lean_dec_ref(v_fixed_4339_);
                    crate::leanh::lean_dec_ref(v_info_4338_);
                    crate::leanh::lean_dec_ref(v_inst_4336_);
                    v_toApplicative_4355_ = crate::leanh::lean_ctor_get(v_inst_4334_, 0);
                    v_toBind_4356_ = crate::leanh::lean_ctor_get(v_inst_4334_, 1);
                    v_isSharedCheck_4417_ = (!crate::leanh::lean_is_exclusive(v_inst_4334_)) as u8;
                    if v_isSharedCheck_4417_ == 0 {
                        v___x_4358_ = v_inst_4334_;
                        v_isShared_4359_ = v_isSharedCheck_4417_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_toBind_4356_);
                        crate::leanh::lean_inc(v_toApplicative_4355_);
                        crate::leanh::lean_dec(v_inst_4334_);
                        v___x_4358_ = crate::leanh::lean_box(0);
                        v_isShared_4359_ = v_isSharedCheck_4417_;
                        state = 2;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_e_4341_) == 8 {
                        v_nondep_4418_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_4341_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                        );
                        if v_nondep_4418_ == 1 {
                            v_declName_4419_ = crate::leanh::lean_ctor_get(v_e_4341_, 0);
                            crate::leanh::lean_inc(v_declName_4419_);
                            v_type_4420_ = crate::leanh::lean_ctor_get(v_e_4341_, 1);
                            crate::leanh::lean_inc_ref(v_type_4420_);
                            v_value_4421_ = crate::leanh::lean_ctor_get(v_e_4341_, 2);
                            crate::leanh::lean_inc_ref(v_value_4421_);
                            v_body_4422_ = crate::leanh::lean_ctor_get(v_e_4341_, 3);
                            crate::leanh::lean_inc_ref(v_body_4422_);
                            crate::leanh::lean_dec_ref_known(v_e_4341_, 4);
                            v_hinfo_4423_ = lean_array_fget_borrowed(v_haveInfo_4349_, v_i_4342_);
                            v_decl_4424_ = crate::leanh::lean_ctor_get(v_hinfo_4423_, 2);
                            v_level_4425_ = crate::leanh::lean_ctor_get(v_hinfo_4423_, 3);
                            crate::leanh::lean_inc_ref(v_decl_4424_);
                            v_x_4426_ = l_Lean_LocalDecl_toExpr(v_decl_4424_);
                            v_val_4427_ = l_Lean_LocalDecl_value(v_decl_4424_, v_nondep_4418_);
                            v___x_4428_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_level_4352_);
                            v___x_4429_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4429_, 0, v_level_4352_);
                            crate::leanh::lean_ctor_set(v___x_4429_, 1, v___x_4428_);
                            crate::leanh::lean_inc_ref(v___x_4429_);
                            crate::leanh::lean_inc(v_level_4425_);
                            v_us_4430_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_us_4430_, 0, v_level_4425_);
                            crate::leanh::lean_ctor_set(v_us_4430_, 1, v___x_4429_);
                            v___x_4459_ = lean_array_get_size(v_used_4340_);
                            v___x_4460_ = lean_nat_dec_lt(v_i_4342_, v___x_4459_);
                            if v___x_4460_ == 0 {
                                crate::leanh::lean_inc_ref(v_decl_4424_);
                                state = 9;
                                continue;
                            } else {
                                v___x_4461_ = lean_array_fget_borrowed(v_used_4340_, v_i_4342_);
                                v___x_4462_ = (crate::leanh::lean_unbox(v___x_4461_) as u8);
                                if v___x_4462_ == 0 {
                                    crate::leanh::lean_dec_ref(v_x_4426_);
                                    v_toApplicative_4463_ =
                                        crate::leanh::lean_ctor_get(v_inst_4334_, 0);
                                    crate::leanh::lean_inc_ref(v_toApplicative_4463_);
                                    v_toBind_4464_ = crate::leanh::lean_ctor_get(v_inst_4334_, 1);
                                    crate::leanh::lean_inc(v_toBind_4464_);
                                    v___x_4465_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
                                    v_toApplicative_4466_ =
                                        crate::leanh::lean_ctor_get(v___x_4465_, 0);
                                    v_toFunctor_4467_ =
                                        crate::leanh::lean_ctor_get(v_toApplicative_4466_, 0);
                                    v_toSeq_4468_ =
                                        crate::leanh::lean_ctor_get(v_toApplicative_4466_, 2);
                                    v_toSeqLeft_4469_ =
                                        crate::leanh::lean_ctor_get(v_toApplicative_4466_, 3);
                                    v_toSeqRight_4470_ =
                                        crate::leanh::lean_ctor_get(v_toApplicative_4466_, 4);
                                    v___f_4471_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2;
                                    v___f_4472_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3;
                                    crate::leanh::lean_inc_ref_n(v_toFunctor_4467_, 2);
                                    v___f_4473_ = crate::leanh::lean_alloc_closure(
                                        l_ReaderT_instFunctorOfMonad___redArg___lam__0
                                            as *mut core::ffi::c_void,
                                        6,
                                        1,
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___f_4473_,
                                        0,
                                        v_toFunctor_4467_,
                                    );
                                    v___f_4474_ = crate::leanh::lean_alloc_closure(
                                        l_ReaderT_instFunctorOfMonad___redArg___lam__1
                                            as *mut core::ffi::c_void,
                                        6,
                                        1,
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___f_4474_,
                                        0,
                                        v_toFunctor_4467_,
                                    );
                                    v___x_4475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4475_, 0, v___f_4473_);
                                    crate::leanh::lean_ctor_set(v___x_4475_, 1, v___f_4474_);
                                    crate::leanh::lean_inc(v_toSeqRight_4470_);
                                    v___f_4476_ = crate::leanh::lean_alloc_closure(
                                        l_ReaderT_instApplicativeOfMonad___redArg___lam__1
                                            as *mut core::ffi::c_void,
                                        6,
                                        1,
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___f_4476_,
                                        0,
                                        v_toSeqRight_4470_,
                                    );
                                    crate::leanh::lean_inc(v_toSeqLeft_4469_);
                                    v___f_4477_ = crate::leanh::lean_alloc_closure(
                                        l_ReaderT_instApplicativeOfMonad___redArg___lam__3
                                            as *mut core::ffi::c_void,
                                        6,
                                        1,
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___f_4477_,
                                        0,
                                        v_toSeqLeft_4469_,
                                    );
                                    crate::leanh::lean_inc(v_toSeq_4468_);
                                    v___f_4478_ = crate::leanh::lean_alloc_closure(
                                        l_ReaderT_instApplicativeOfMonad___redArg___lam__4
                                            as *mut core::ffi::c_void,
                                        6,
                                        1,
                                    );
                                    crate::leanh::lean_closure_set(v___f_4478_, 0, v_toSeq_4468_);
                                    v___x_4479_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4479_, 0, v___x_4475_);
                                    crate::leanh::lean_ctor_set(v___x_4479_, 1, v___f_4471_);
                                    crate::leanh::lean_ctor_set(v___x_4479_, 2, v___f_4478_);
                                    crate::leanh::lean_ctor_set(v___x_4479_, 3, v___f_4477_);
                                    crate::leanh::lean_ctor_set(v___x_4479_, 4, v___f_4476_);
                                    v___x_4480_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4480_, 0, v___x_4479_);
                                    crate::leanh::lean_ctor_set(v___x_4480_, 1, v___f_4472_);
                                    v___x_4481_ = l_StateRefT_x27_instMonad___redArg(v___x_4480_);
                                    v_toApplicative_4482_ =
                                        crate::leanh::lean_ctor_get(v___x_4481_, 0);
                                    v_isSharedCheck_4518_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4481_)) as u8;
                                    if v_isSharedCheck_4518_ == 0 {
                                        v_unused_4519_ =
                                            crate::leanh::lean_ctor_get(v___x_4481_, 1);
                                        crate::leanh::lean_dec(v_unused_4519_);
                                        v___x_4484_ = v___x_4481_;
                                        v_isShared_4485_ = v_isSharedCheck_4518_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_toApplicative_4482_);
                                        crate::leanh::lean_dec(v___x_4481_);
                                        v___x_4484_ = crate::leanh::lean_box(0);
                                        v_isShared_4485_ = v_isSharedCheck_4518_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc_ref(v_decl_4424_);
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_4341_, 4);
                            crate::leanh::lean_dec_ref(v_xs_4343_);
                            crate::leanh::lean_dec(v_i_4342_);
                            crate::leanh::lean_dec_ref(v_used_4340_);
                            crate::leanh::lean_dec_ref(v_fixed_4339_);
                            crate::leanh::lean_dec_ref(v_info_4338_);
                            crate::leanh::lean_dec_ref(v_inst_4337_);
                            crate::leanh::lean_dec_ref(v_inst_4336_);
                            crate::leanh::lean_dec(v_inst_4335_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_xs_4343_);
                        crate::leanh::lean_dec(v_i_4342_);
                        crate::leanh::lean_dec_ref(v_e_4341_);
                        crate::leanh::lean_dec_ref(v_used_4340_);
                        crate::leanh::lean_dec_ref(v_fixed_4339_);
                        crate::leanh::lean_dec_ref(v_info_4338_);
                        crate::leanh::lean_dec_ref(v_inst_4337_);
                        crate::leanh::lean_dec_ref(v_inst_4336_);
                        crate::leanh::lean_dec(v_inst_4335_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4345_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
                v___x_4346_ = l_instInhabitedOfMonad___redArg(v_inst_4334_, v___x_4345_);
                v___x_4347_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
                v___x_4348_ = l_panic___redArg(v___x_4346_, v___x_4347_);
                crate::leanh::lean_dec(v___x_4346_);
                return v___x_4348_;
            }
            2 => {
                v___x_4360_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
                v_toApplicative_4361_ = crate::leanh::lean_ctor_get(v___x_4360_, 0);
                v_toFunctor_4362_ = crate::leanh::lean_ctor_get(v_toApplicative_4361_, 0);
                v_toSeq_4363_ = crate::leanh::lean_ctor_get(v_toApplicative_4361_, 2);
                v_toSeqLeft_4364_ = crate::leanh::lean_ctor_get(v_toApplicative_4361_, 3);
                v_toSeqRight_4365_ = crate::leanh::lean_ctor_get(v_toApplicative_4361_, 4);
                v___f_4366_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2;
                v___f_4367_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_4362_, 2);
                v___f_4368_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4368_, 0, v_toFunctor_4362_);
                v___f_4369_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4369_, 0, v_toFunctor_4362_);
                v___x_4370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4370_, 0, v___f_4368_);
                crate::leanh::lean_ctor_set(v___x_4370_, 1, v___f_4369_);
                crate::leanh::lean_inc(v_toSeqRight_4365_);
                v___f_4371_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4371_, 0, v_toSeqRight_4365_);
                crate::leanh::lean_inc(v_toSeqLeft_4364_);
                v___f_4372_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4372_, 0, v_toSeqLeft_4364_);
                crate::leanh::lean_inc(v_toSeq_4363_);
                v___f_4373_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4373_, 0, v_toSeq_4363_);
                v___x_4374_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4374_, 0, v___x_4370_);
                crate::leanh::lean_ctor_set(v___x_4374_, 1, v___f_4366_);
                crate::leanh::lean_ctor_set(v___x_4374_, 2, v___f_4373_);
                crate::leanh::lean_ctor_set(v___x_4374_, 3, v___f_4372_);
                crate::leanh::lean_ctor_set(v___x_4374_, 4, v___f_4371_);
                if v_isShared_4359_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4358_, 1, v___f_4367_);
                    crate::leanh::lean_ctor_set(v___x_4358_, 0, v___x_4374_);
                    v___x_4376_ = v___x_4358_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4416_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___f_4367_);
                    v___x_4376_ = v_reuseFailAlloc_4416_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4377_ = l_StateRefT_x27_instMonad___redArg(v___x_4376_);
                v_toApplicative_4378_ = crate::leanh::lean_ctor_get(v___x_4377_, 0);
                v_isSharedCheck_4414_ = (!crate::leanh::lean_is_exclusive(v___x_4377_)) as u8;
                if v_isSharedCheck_4414_ == 0 {
                    v_unused_4415_ = crate::leanh::lean_ctor_get(v___x_4377_, 1);
                    crate::leanh::lean_dec(v_unused_4415_);
                    v___x_4380_ = v___x_4377_;
                    v_isShared_4381_ = v_isSharedCheck_4414_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4378_);
                    crate::leanh::lean_dec(v___x_4377_);
                    v___x_4380_ = crate::leanh::lean_box(0);
                    v_isShared_4381_ = v_isSharedCheck_4414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_toFunctor_4382_ = crate::leanh::lean_ctor_get(v_toApplicative_4378_, 0);
                v_toSeq_4383_ = crate::leanh::lean_ctor_get(v_toApplicative_4378_, 2);
                v_toSeqLeft_4384_ = crate::leanh::lean_ctor_get(v_toApplicative_4378_, 3);
                v_toSeqRight_4385_ = crate::leanh::lean_ctor_get(v_toApplicative_4378_, 4);
                v_isSharedCheck_4412_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4378_)) as u8;
                if v_isSharedCheck_4412_ == 0 {
                    v_unused_4413_ = crate::leanh::lean_ctor_get(v_toApplicative_4378_, 1);
                    crate::leanh::lean_dec(v_unused_4413_);
                    v___x_4387_ = v_toApplicative_4378_;
                    v_isShared_4388_ = v_isSharedCheck_4412_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4385_);
                    crate::leanh::lean_inc(v_toSeqLeft_4384_);
                    crate::leanh::lean_inc(v_toSeq_4383_);
                    crate::leanh::lean_inc(v_toFunctor_4382_);
                    crate::leanh::lean_dec(v_toApplicative_4378_);
                    v___x_4387_ = crate::leanh::lean_box(0);
                    v_isShared_4388_ = v_isSharedCheck_4412_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4389_ = crate::leanh::lean_box((v___x_4354_) as usize);
                crate::leanh::lean_inc(v_toBind_4356_);
                crate::leanh::lean_inc_ref(v_body_4350_);
                v___f_4390_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 10, 9);
                crate::leanh::lean_closure_set(v___f_4390_, 0, v_inst_4337_);
                crate::leanh::lean_closure_set(v___f_4390_, 1, v_bodyType_4351_);
                crate::leanh::lean_closure_set(v___f_4390_, 2, v_xs_4343_);
                crate::leanh::lean_closure_set(v___f_4390_, 3, v_toApplicative_4355_);
                crate::leanh::lean_closure_set(v___f_4390_, 4, v_level_4352_);
                crate::leanh::lean_closure_set(v___f_4390_, 5, v_e_4341_);
                crate::leanh::lean_closure_set(v___f_4390_, 6, v___x_4389_);
                crate::leanh::lean_closure_set(v___f_4390_, 7, v_body_4350_);
                crate::leanh::lean_closure_set(v___f_4390_, 8, v_toBind_4356_);
                v_cls_4391_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8;
                v___f_4392_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9;
                v___f_4393_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10;
                crate::leanh::lean_inc_ref(v_toFunctor_4382_);
                v___f_4394_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4394_, 0, v_toFunctor_4382_);
                v___f_4395_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4395_, 0, v_toFunctor_4382_);
                v___x_4396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4396_, 0, v___f_4394_);
                crate::leanh::lean_ctor_set(v___x_4396_, 1, v___f_4395_);
                v___f_4397_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4397_, 0, v_toSeqRight_4385_);
                v___f_4398_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4398_, 0, v_toSeqLeft_4384_);
                v___f_4399_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4399_, 0, v_toSeq_4383_);
                if v_isShared_4388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4387_, 4, v___f_4397_);
                    crate::leanh::lean_ctor_set(v___x_4387_, 3, v___f_4398_);
                    crate::leanh::lean_ctor_set(v___x_4387_, 2, v___f_4399_);
                    crate::leanh::lean_ctor_set(v___x_4387_, 1, v___f_4392_);
                    crate::leanh::lean_ctor_set(v___x_4387_, 0, v___x_4396_);
                    v___x_4401_ = v___x_4387_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4411_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 1, v___f_4392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 2, v___f_4399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 3, v___f_4398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 4, v___f_4397_);
                    v___x_4401_ = v_reuseFailAlloc_4411_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4381_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4380_, 1, v___f_4393_);
                    crate::leanh::lean_ctor_set(v___x_4380_, 0, v___x_4401_);
                    v___x_4403_ = v___x_4380_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4410_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4410_, 1, v___f_4393_);
                    v___x_4403_ = v_reuseFailAlloc_4410_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___f_4404_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11;
                v___x_4405_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12;
                v___x_4406_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
                v___f_4407_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed as *mut core::ffi::c_void, 11, 6);
                crate::leanh::lean_closure_set(v___f_4407_, 0, v_cls_4391_);
                crate::leanh::lean_closure_set(v___f_4407_, 1, v___x_4405_);
                crate::leanh::lean_closure_set(v___f_4407_, 2, v___f_4404_);
                crate::leanh::lean_closure_set(v___f_4407_, 3, v_body_4350_);
                crate::leanh::lean_closure_set(v___f_4407_, 4, v___x_4403_);
                crate::leanh::lean_closure_set(v___f_4407_, 5, v___x_4406_);
                v___x_4408_ = crate::leanh::lean_apply_2(
                    v_inst_4335_,
                    crate::leanh::lean_box(0),
                    v___f_4407_,
                );
                v___x_4409_ = crate::leanh::lean_apply_4(
                    v_toBind_4356_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4408_,
                    v___f_4390_,
                );
                return v___x_4409_;
            }
            8 => {
                v_toApplicative_4433_ = crate::leanh::lean_ctor_get(v_inst_4334_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4433_);
                v_toBind_4434_ = crate::leanh::lean_ctor_get(v_inst_4334_, 1);
                crate::leanh::lean_inc_n(v_toBind_4434_, 2);
                v_withNewLemmas_4435_ = crate::leanh::lean_ctor_get(v_inst_4337_, 0);
                crate::leanh::lean_inc(v_withNewLemmas_4435_);
                v_dsimp_4436_ = crate::leanh::lean_ctor_get(v_inst_4337_, 1);
                crate::leanh::lean_inc(v_dsimp_4436_);
                v___x_4437_ = crate::leanh::lean_box((v_nondep_4418_) as usize);
                v___x_4438_ = crate::leanh::lean_box((v___y_4432_) as usize);
                crate::leanh::lean_inc_ref(v_val_4427_);
                v___f_4439_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed as *mut core::ffi::c_void, 24, 23);
                crate::leanh::lean_closure_set(v___f_4439_, 0, v_declName_4419_);
                crate::leanh::lean_closure_set(v___f_4439_, 1, v_type_4420_);
                crate::leanh::lean_closure_set(v___f_4439_, 2, v_value_4421_);
                crate::leanh::lean_closure_set(v___f_4439_, 3, v___x_4437_);
                crate::leanh::lean_closure_set(v___f_4439_, 4, v_toApplicative_4433_);
                crate::leanh::lean_closure_set(v___f_4439_, 5, v___x_4429_);
                crate::leanh::lean_closure_set(v___f_4439_, 6, v_us_4430_);
                crate::leanh::lean_closure_set(v___f_4439_, 7, v_decl_4424_);
                crate::leanh::lean_closure_set(v___f_4439_, 8, v_x_4426_);
                crate::leanh::lean_closure_set(v___f_4439_, 9, v_i_4342_);
                crate::leanh::lean_closure_set(v___f_4439_, 10, v_xs_4343_);
                crate::leanh::lean_closure_set(v___f_4439_, 11, v_inst_4334_);
                crate::leanh::lean_closure_set(v___f_4439_, 12, v_inst_4335_);
                crate::leanh::lean_closure_set(v___f_4439_, 13, v_inst_4336_);
                crate::leanh::lean_closure_set(v___f_4439_, 14, v_inst_4337_);
                crate::leanh::lean_closure_set(v___f_4439_, 15, v_info_4338_);
                crate::leanh::lean_closure_set(v___f_4439_, 16, v_fixed_4339_);
                crate::leanh::lean_closure_set(v___f_4439_, 17, v_used_4340_);
                crate::leanh::lean_closure_set(v___f_4439_, 18, v_body_4422_);
                crate::leanh::lean_closure_set(v___f_4439_, 19, v_toBind_4434_);
                crate::leanh::lean_closure_set(v___f_4439_, 20, v_withNewLemmas_4435_);
                crate::leanh::lean_closure_set(v___f_4439_, 21, v_val_4427_);
                crate::leanh::lean_closure_set(v___f_4439_, 22, v___x_4438_);
                v___x_4440_ = crate::leanh::lean_apply_1(v_dsimp_4436_, v_val_4427_);
                v___x_4441_ = crate::leanh::lean_apply_4(
                    v_toBind_4434_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4440_,
                    v___f_4439_,
                );
                return v___x_4441_;
            }
            9 => {
                v___x_4443_ = 0;
                v___x_4444_ = lean_array_get_size(v_fixed_4339_);
                v___x_4445_ = lean_nat_dec_lt(v_i_4342_, v___x_4444_);
                if v___x_4445_ == 0 {
                    v___y_4432_ = v___x_4443_;
                    state = 8;
                    continue;
                } else {
                    v___x_4446_ = lean_array_fget_borrowed(v_fixed_4339_, v_i_4342_);
                    v___x_4447_ = (crate::leanh::lean_unbox(v___x_4446_) as u8);
                    if v___x_4447_ == 0 {
                        crate::leanh::lean_inc(v___x_4446_);
                        crate::leanh::lean_inc(v_level_4425_);
                        v_toApplicative_4448_ = crate::leanh::lean_ctor_get(v_inst_4334_, 0);
                        crate::leanh::lean_inc_ref_n(v_toApplicative_4448_, 2);
                        v_toBind_4449_ = crate::leanh::lean_ctor_get(v_inst_4334_, 1);
                        crate::leanh::lean_inc_n(v_toBind_4449_, 3);
                        v_withNewLemmas_4450_ = crate::leanh::lean_ctor_get(v_inst_4337_, 0);
                        crate::leanh::lean_inc(v_withNewLemmas_4450_);
                        v_simp_4451_ = crate::leanh::lean_ctor_get(v_inst_4337_, 2);
                        crate::leanh::lean_inc(v_simp_4451_);
                        v___x_4452_ = crate::leanh::lean_box((v_nondep_4418_) as usize);
                        crate::leanh::lean_inc(v_inst_4335_);
                        crate::leanh::lean_inc_ref(v_xs_4343_);
                        crate::leanh::lean_inc_ref(v_value_4421_);
                        crate::leanh::lean_inc_ref(v_type_4420_);
                        crate::leanh::lean_inc(v_declName_4419_);
                        v___f_4453_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed as *mut core::ffi::c_void, 22, 21);
                        crate::leanh::lean_closure_set(v___f_4453_, 0, v_decl_4424_);
                        crate::leanh::lean_closure_set(v___f_4453_, 1, v_declName_4419_);
                        crate::leanh::lean_closure_set(v___f_4453_, 2, v_type_4420_);
                        crate::leanh::lean_closure_set(v___f_4453_, 3, v_value_4421_);
                        crate::leanh::lean_closure_set(v___f_4453_, 4, v___x_4452_);
                        crate::leanh::lean_closure_set(v___f_4453_, 5, v_toApplicative_4448_);
                        crate::leanh::lean_closure_set(v___f_4453_, 6, v___x_4429_);
                        crate::leanh::lean_closure_set(v___f_4453_, 7, v_us_4430_);
                        crate::leanh::lean_closure_set(v___f_4453_, 8, v_inst_4334_);
                        crate::leanh::lean_closure_set(v___f_4453_, 9, v_x_4426_);
                        crate::leanh::lean_closure_set(v___f_4453_, 10, v_i_4342_);
                        crate::leanh::lean_closure_set(v___f_4453_, 11, v_xs_4343_);
                        crate::leanh::lean_closure_set(v___f_4453_, 12, v_inst_4335_);
                        crate::leanh::lean_closure_set(v___f_4453_, 13, v_inst_4336_);
                        crate::leanh::lean_closure_set(v___f_4453_, 14, v_inst_4337_);
                        crate::leanh::lean_closure_set(v___f_4453_, 15, v_info_4338_);
                        crate::leanh::lean_closure_set(v___f_4453_, 16, v_fixed_4339_);
                        crate::leanh::lean_closure_set(v___f_4453_, 17, v_used_4340_);
                        crate::leanh::lean_closure_set(v___f_4453_, 18, v_body_4422_);
                        crate::leanh::lean_closure_set(v___f_4453_, 19, v_toBind_4449_);
                        crate::leanh::lean_closure_set(v___f_4453_, 20, v_withNewLemmas_4450_);
                        v___f_4454_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_4454_, 0, v___f_4453_);
                        v___x_4455_ = crate::leanh::lean_box((v_nondep_4418_) as usize);
                        crate::leanh::lean_inc_ref(v_val_4427_);
                        crate::leanh::lean_inc_ref(v___f_4454_);
                        v___f_4456_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed as *mut core::ffi::c_void, 15, 14);
                        crate::leanh::lean_closure_set(v___f_4456_, 0, v_toApplicative_4448_);
                        crate::leanh::lean_closure_set(v___f_4456_, 1, v_level_4425_);
                        crate::leanh::lean_closure_set(v___f_4456_, 2, v___x_4428_);
                        crate::leanh::lean_closure_set(v___f_4456_, 3, v_type_4420_);
                        crate::leanh::lean_closure_set(v___f_4456_, 4, v_value_4421_);
                        crate::leanh::lean_closure_set(v___f_4456_, 5, v___x_4446_);
                        crate::leanh::lean_closure_set(v___f_4456_, 6, v_toBind_4449_);
                        crate::leanh::lean_closure_set(v___f_4456_, 7, v___f_4454_);
                        crate::leanh::lean_closure_set(v___f_4456_, 8, v_xs_4343_);
                        crate::leanh::lean_closure_set(v___f_4456_, 9, v___x_4455_);
                        crate::leanh::lean_closure_set(v___f_4456_, 10, v___f_4454_);
                        crate::leanh::lean_closure_set(v___f_4456_, 11, v_declName_4419_);
                        crate::leanh::lean_closure_set(v___f_4456_, 12, v_val_4427_);
                        crate::leanh::lean_closure_set(v___f_4456_, 13, v_inst_4335_);
                        v___x_4457_ = crate::leanh::lean_apply_1(v_simp_4451_, v_val_4427_);
                        v___x_4458_ = crate::leanh::lean_apply_4(
                            v_toBind_4449_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4457_,
                            v___f_4456_,
                        );
                        return v___x_4458_;
                    } else {
                        v___y_4432_ = v___x_4443_;
                        state = 8;
                        continue;
                    }
                }
            }
            10 => {
                v_toFunctor_4486_ = crate::leanh::lean_ctor_get(v_toApplicative_4482_, 0);
                v_toSeq_4487_ = crate::leanh::lean_ctor_get(v_toApplicative_4482_, 2);
                v_toSeqLeft_4488_ = crate::leanh::lean_ctor_get(v_toApplicative_4482_, 3);
                v_toSeqRight_4489_ = crate::leanh::lean_ctor_get(v_toApplicative_4482_, 4);
                v_isSharedCheck_4516_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4482_)) as u8;
                if v_isSharedCheck_4516_ == 0 {
                    v_unused_4517_ = crate::leanh::lean_ctor_get(v_toApplicative_4482_, 1);
                    crate::leanh::lean_dec(v_unused_4517_);
                    v___x_4491_ = v_toApplicative_4482_;
                    v_isShared_4492_ = v_isSharedCheck_4516_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4489_);
                    crate::leanh::lean_inc(v_toSeqLeft_4488_);
                    crate::leanh::lean_inc(v_toSeq_4487_);
                    crate::leanh::lean_inc(v_toFunctor_4486_);
                    crate::leanh::lean_dec(v_toApplicative_4482_);
                    v___x_4491_ = crate::leanh::lean_box(0);
                    v_isShared_4492_ = v_isSharedCheck_4516_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4493_ = crate::leanh::lean_box((v_nondep_4418_) as usize);
                crate::leanh::lean_inc(v_toBind_4464_);
                crate::leanh::lean_inc(v_inst_4335_);
                crate::leanh::lean_inc(v_declName_4419_);
                v___f_4494_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed as *mut core::ffi::c_void, 20, 19);
                crate::leanh::lean_closure_set(v___f_4494_, 0, v___x_4428_);
                crate::leanh::lean_closure_set(v___f_4494_, 1, v_declName_4419_);
                crate::leanh::lean_closure_set(v___f_4494_, 2, v_type_4420_);
                crate::leanh::lean_closure_set(v___f_4494_, 3, v_value_4421_);
                crate::leanh::lean_closure_set(v___f_4494_, 4, v_us_4430_);
                crate::leanh::lean_closure_set(v___f_4494_, 5, v___x_4429_);
                crate::leanh::lean_closure_set(v___f_4494_, 6, v_toApplicative_4463_);
                crate::leanh::lean_closure_set(v___f_4494_, 7, v___x_4493_);
                crate::leanh::lean_closure_set(v___f_4494_, 8, v_i_4342_);
                crate::leanh::lean_closure_set(v___f_4494_, 9, v_xs_4343_);
                crate::leanh::lean_closure_set(v___f_4494_, 10, v_inst_4334_);
                crate::leanh::lean_closure_set(v___f_4494_, 11, v_inst_4335_);
                crate::leanh::lean_closure_set(v___f_4494_, 12, v_inst_4336_);
                crate::leanh::lean_closure_set(v___f_4494_, 13, v_inst_4337_);
                crate::leanh::lean_closure_set(v___f_4494_, 14, v_info_4338_);
                crate::leanh::lean_closure_set(v___f_4494_, 15, v_fixed_4339_);
                crate::leanh::lean_closure_set(v___f_4494_, 16, v_used_4340_);
                crate::leanh::lean_closure_set(v___f_4494_, 17, v_body_4422_);
                crate::leanh::lean_closure_set(v___f_4494_, 18, v_toBind_4464_);
                v_cls_4495_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8;
                v___f_4496_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9;
                v___f_4497_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10;
                crate::leanh::lean_inc_ref(v_toFunctor_4486_);
                v___f_4498_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4498_, 0, v_toFunctor_4486_);
                v___f_4499_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4499_, 0, v_toFunctor_4486_);
                v___x_4500_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4500_, 0, v___f_4498_);
                crate::leanh::lean_ctor_set(v___x_4500_, 1, v___f_4499_);
                v___f_4501_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4501_, 0, v_toSeqRight_4489_);
                v___f_4502_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4502_, 0, v_toSeqLeft_4488_);
                v___f_4503_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4503_, 0, v_toSeq_4487_);
                if v_isShared_4492_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4491_, 4, v___f_4501_);
                    crate::leanh::lean_ctor_set(v___x_4491_, 3, v___f_4502_);
                    crate::leanh::lean_ctor_set(v___x_4491_, 2, v___f_4503_);
                    crate::leanh::lean_ctor_set(v___x_4491_, 1, v___f_4496_);
                    crate::leanh::lean_ctor_set(v___x_4491_, 0, v___x_4500_);
                    v___x_4505_ = v___x_4491_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4515_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 1, v___f_4496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 2, v___f_4503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 3, v___f_4502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 4, v___f_4501_);
                    v___x_4505_ = v_reuseFailAlloc_4515_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4485_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4484_, 1, v___f_4497_);
                    crate::leanh::lean_ctor_set(v___x_4484_, 0, v___x_4505_);
                    v___x_4507_ = v___x_4484_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4514_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 1, v___f_4497_);
                    v___x_4507_ = v_reuseFailAlloc_4514_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___f_4508_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11;
                v___x_4509_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12;
                v___x_4510_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
                v___f_4511_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed as *mut core::ffi::c_void, 12, 7);
                crate::leanh::lean_closure_set(v___f_4511_, 0, v_cls_4495_);
                crate::leanh::lean_closure_set(v___f_4511_, 1, v___x_4509_);
                crate::leanh::lean_closure_set(v___f_4511_, 2, v___f_4508_);
                crate::leanh::lean_closure_set(v___f_4511_, 3, v_declName_4419_);
                crate::leanh::lean_closure_set(v___f_4511_, 4, v_val_4427_);
                crate::leanh::lean_closure_set(v___f_4511_, 5, v___x_4507_);
                crate::leanh::lean_closure_set(v___f_4511_, 6, v___x_4510_);
                v___x_4512_ = crate::leanh::lean_apply_2(
                    v_inst_4335_,
                    crate::leanh::lean_box(0),
                    v___f_4511_,
                );
                v___x_4513_ = crate::leanh::lean_apply_4(
                    v_toBind_4464_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4512_,
                    v___f_4494_,
                );
                return v___x_4513_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(
    mut v___x_4520_: *mut crate::leanh::LeanObject,
    mut v_declName_4521_: *mut crate::leanh::LeanObject,
    mut v_type_4522_: *mut crate::leanh::LeanObject,
    mut v_value_4523_: *mut crate::leanh::LeanObject,
    mut v_us_4524_: *mut crate::leanh::LeanObject,
    mut v___x_4525_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_4526_: *mut crate::leanh::LeanObject,
    mut v_nondep_4527_: u8,
    mut v_i_4528_: *mut crate::leanh::LeanObject,
    mut v_xs_4529_: *mut crate::leanh::LeanObject,
    mut v_inst_4530_: *mut crate::leanh::LeanObject,
    mut v_inst_4531_: *mut crate::leanh::LeanObject,
    mut v_inst_4532_: *mut crate::leanh::LeanObject,
    mut v_inst_4533_: *mut crate::leanh::LeanObject,
    mut v_info_4534_: *mut crate::leanh::LeanObject,
    mut v_fixed_4535_: *mut crate::leanh::LeanObject,
    mut v_used_4536_: *mut crate::leanh::LeanObject,
    mut v_body_4537_: *mut crate::leanh::LeanObject,
    mut v_toBind_4538_: *mut crate::leanh::LeanObject,
    mut v_____r_4539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4540_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1;
    v_x_4541_ = l_Lean_mkConst(v___x_4540_, v___x_4520_);
    v___x_4542_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4543_ = crate::leanh::lean_box((v_nondep_4527_) as usize);
    v___f_4544_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed as *mut core::ffi::c_void, 9, 8);
    crate::leanh::lean_closure_set(v___f_4544_, 0, v___x_4542_);
    crate::leanh::lean_closure_set(v___f_4544_, 1, v_declName_4521_);
    crate::leanh::lean_closure_set(v___f_4544_, 2, v_type_4522_);
    crate::leanh::lean_closure_set(v___f_4544_, 3, v_value_4523_);
    crate::leanh::lean_closure_set(v___f_4544_, 4, v_us_4524_);
    crate::leanh::lean_closure_set(v___f_4544_, 5, v___x_4525_);
    crate::leanh::lean_closure_set(v___f_4544_, 6, v_toApplicative_4526_);
    crate::leanh::lean_closure_set(v___f_4544_, 7, v___x_4543_);
    v___x_4545_ = lean_nat_add(v_i_4528_, v___x_4542_);
    v___x_4546_ = lean_array_push(v_xs_4529_, v_x_4541_);
    v___x_4547_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(
        v_inst_4530_,
        v_inst_4531_,
        v_inst_4532_,
        v_inst_4533_,
        v_info_4534_,
        v_fixed_4535_,
        v_used_4536_,
        v_body_4537_,
        v___x_4545_,
        v___x_4546_,
    );
    v___x_4548_ = crate::leanh::lean_apply_4(
        v_toBind_4538_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4547_,
        v___f_4544_,
    );
    return v___x_4548_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(
    mut v_m_4549_: *mut crate::leanh::LeanObject,
    mut v_inst_4550_: *mut crate::leanh::LeanObject,
    mut v_inst_4551_: *mut crate::leanh::LeanObject,
    mut v_inst_4552_: *mut crate::leanh::LeanObject,
    mut v_inst_4553_: *mut crate::leanh::LeanObject,
    mut v_info_4554_: *mut crate::leanh::LeanObject,
    mut v_fixed_4555_: *mut crate::leanh::LeanObject,
    mut v_used_4556_: *mut crate::leanh::LeanObject,
    mut v_e_4557_: *mut crate::leanh::LeanObject,
    mut v_i_4558_: *mut crate::leanh::LeanObject,
    mut v_xs_4559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4560_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(
        v_inst_4550_,
        v_inst_4551_,
        v_inst_4552_,
        v_inst_4553_,
        v_info_4554_,
        v_fixed_4555_,
        v_used_4556_,
        v_e_4557_,
        v_i_4558_,
        v_xs_4559_,
    );
    return v___x_4560_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_ctorIdx(
    mut v_x_4561_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_4561_ {
        0 => {
            let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4562_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4562_;
        }
        1 => {
            let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4563_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4563_;
        }
        _ => {
            let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4564_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4564_;
        }
    }
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(
    mut v_x_4565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4566_: u8 = 0;
    let mut v_res_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4566_ = (crate::leanh::lean_unbox(v_x_4565_) as u8);
    v_res_4567_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_4566_);
    return v_res_4567_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_toCtorIdx(
    mut v_x_4568_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4569_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_4568_);
    return v___x_4569_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_toCtorIdx___boxed(
    mut v_x_4570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_4571_: u8 = 0;
    let mut v_res_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4571_ = (crate::leanh::lean_unbox(v_x_4570_) as u8);
    v_res_4572_ = l_Lean_Meta_ZetaUnusedMode_toCtorIdx(v_x_4__boxed_4571_);
    return v_res_4572_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(
    mut v_k_4573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4573_);
    return v_k_4573_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(
    mut v_k_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4575_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_4574_);
    crate::leanh::lean_dec(v_k_4574_);
    return v_res_4575_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_ctorElim(
    mut v_motive_4576_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4577_: *mut crate::leanh::LeanObject,
    mut v_t_4578_: u8,
    mut v_h_4579_: *mut crate::leanh::LeanObject,
    mut v_k_4580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4580_);
    return v_k_4580_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(
    mut v_motive_4581_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4582_: *mut crate::leanh::LeanObject,
    mut v_t_4583_: *mut crate::leanh::LeanObject,
    mut v_h_4584_: *mut crate::leanh::LeanObject,
    mut v_k_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4586_: u8 = 0;
    let mut v_res_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4586_ = (crate::leanh::lean_unbox(v_t_4583_) as u8);
    v_res_4587_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(
        v_motive_4581_,
        v_ctorIdx_4582_,
        v_t_boxed_4586_,
        v_h_4584_,
        v_k_4585_,
    );
    crate::leanh::lean_dec(v_k_4585_);
    crate::leanh::lean_dec(v_ctorIdx_4582_);
    return v_res_4587_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(
    mut v_no_4588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_no_4588_);
    return v_no_4588_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(
    mut v_no_4589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4590_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_4589_);
    crate::leanh::lean_dec(v_no_4589_);
    return v_res_4590_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_no_elim(
    mut v_motive_4591_: *mut crate::leanh::LeanObject,
    mut v_t_4592_: u8,
    mut v_h_4593_: *mut crate::leanh::LeanObject,
    mut v_no_4594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_no_4594_);
    return v_no_4594_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(
    mut v_motive_4595_: *mut crate::leanh::LeanObject,
    mut v_t_4596_: *mut crate::leanh::LeanObject,
    mut v_h_4597_: *mut crate::leanh::LeanObject,
    mut v_no_4598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4599_: u8 = 0;
    let mut v_res_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4599_ = (crate::leanh::lean_unbox(v_t_4596_) as u8);
    v_res_4600_ =
        l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_4595_, v_t_boxed_4599_, v_h_4597_, v_no_4598_);
    crate::leanh::lean_dec(v_no_4598_);
    return v_res_4600_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(
    mut v_singlePass_4601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_singlePass_4601_);
    return v_singlePass_4601_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(
    mut v_singlePass_4602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4603_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_4602_);
    crate::leanh::lean_dec(v_singlePass_4602_);
    return v_res_4603_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_singlePass_elim(
    mut v_motive_4604_: *mut crate::leanh::LeanObject,
    mut v_t_4605_: u8,
    mut v_h_4606_: *mut crate::leanh::LeanObject,
    mut v_singlePass_4607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_singlePass_4607_);
    return v_singlePass_4607_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(
    mut v_motive_4608_: *mut crate::leanh::LeanObject,
    mut v_t_4609_: *mut crate::leanh::LeanObject,
    mut v_h_4610_: *mut crate::leanh::LeanObject,
    mut v_singlePass_4611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4612_: u8 = 0;
    let mut v_res_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4612_ = (crate::leanh::lean_unbox(v_t_4609_) as u8);
    v_res_4613_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(
        v_motive_4608_,
        v_t_boxed_4612_,
        v_h_4610_,
        v_singlePass_4611_,
    );
    crate::leanh::lean_dec(v_singlePass_4611_);
    return v_res_4613_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(
    mut v_twoPasses_4614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_twoPasses_4614_);
    return v_twoPasses_4614_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(
    mut v_twoPasses_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4616_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_4615_);
    crate::leanh::lean_dec(v_twoPasses_4615_);
    return v_res_4616_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(
    mut v_motive_4617_: *mut crate::leanh::LeanObject,
    mut v_t_4618_: u8,
    mut v_h_4619_: *mut crate::leanh::LeanObject,
    mut v_twoPasses_4620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_twoPasses_4620_);
    return v_twoPasses_4620_;
}
pub unsafe fn l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(
    mut v_motive_4621_: *mut crate::leanh::LeanObject,
    mut v_t_4622_: *mut crate::leanh::LeanObject,
    mut v_h_4623_: *mut crate::leanh::LeanObject,
    mut v_twoPasses_4624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4625_: u8 = 0;
    let mut v_res_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4625_ = (crate::leanh::lean_unbox(v_t_4622_) as u8);
    v_res_4626_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(
        v_motive_4621_,
        v_t_boxed_4625_,
        v_h_4623_,
        v_twoPasses_4624_,
    );
    crate::leanh::lean_dec(v_twoPasses_4624_);
    return v_res_4626_;
}
pub unsafe fn l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(
    mut v_k_4627_: *mut crate::leanh::LeanObject,
    mut v_b_4628_: *mut crate::leanh::LeanObject,
    mut v_c_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4633_);
    crate::leanh::lean_inc_ref(v___y_4632_);
    crate::leanh::lean_inc(v___y_4631_);
    crate::leanh::lean_inc_ref(v___y_4630_);
    v___x_4635_ = crate::leanh::lean_apply_7(
        v_k_4627_,
        v_b_4628_,
        v_c_4629_,
        v___y_4630_,
        v___y_4631_,
        v___y_4632_,
        v___y_4633_,
        crate::leanh::lean_box(0),
    );
    return v___x_4635_;
}
pub unsafe fn l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(
    mut v_k_4636_: *mut crate::leanh::LeanObject,
    mut v_b_4637_: *mut crate::leanh::LeanObject,
    mut v_c_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
    mut v___y_4641_: *mut crate::leanh::LeanObject,
    mut v___y_4642_: *mut crate::leanh::LeanObject,
    mut v___y_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4644_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(
        v_k_4636_,
        v_b_4637_,
        v_c_4638_,
        v___y_4639_,
        v___y_4640_,
        v___y_4641_,
        v___y_4642_,
    );
    crate::leanh::lean_dec(v___y_4642_);
    crate::leanh::lean_dec_ref(v___y_4641_);
    crate::leanh::lean_dec(v___y_4640_);
    crate::leanh::lean_dec_ref(v___y_4639_);
    return v_res_4644_;
}
pub unsafe fn l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(
    mut v_e_4645_: *mut crate::leanh::LeanObject,
    mut v_k_4646_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4647_: u8,
    mut v_preserveNondepLet_4648_: u8,
    mut v_nondepLetOnly_4649_: u8,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut v___x_4657_: u8 = 0;
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4663_: u8 = 0;
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4667_: u8 = 0;
    let mut v_a_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4671_: u8 = 0;
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4655_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_4655_, 0, v_k_4646_);
                v___x_4656_ = 0;
                v___x_4657_ = 1;
                v___x_4658_ = crate::leanh::lean_box(0);
                v___x_4659_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    crate::leanh::lean_box(0),
                    v_e_4645_,
                    v___x_4656_,
                    v___x_4657_,
                    v_preserveNondepLet_4648_,
                    v_nondepLetOnly_4649_,
                    v___x_4658_,
                    v___f_4655_,
                    v_cleanupAnnotations_4647_,
                    v___y_4650_,
                    v___y_4651_,
                    v___y_4652_,
                    v___y_4653_,
                );
                if crate::leanh::lean_obj_tag(v___x_4659_) == 0 {
                    v_a_4660_ = crate::leanh::lean_ctor_get(v___x_4659_, 0);
                    v_isSharedCheck_4667_ = (!crate::leanh::lean_is_exclusive(v___x_4659_)) as u8;
                    if v_isSharedCheck_4667_ == 0 {
                        v___x_4662_ = v___x_4659_;
                        v_isShared_4663_ = v_isSharedCheck_4667_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4660_);
                        crate::leanh::lean_dec(v___x_4659_);
                        v___x_4662_ = crate::leanh::lean_box(0);
                        v_isShared_4663_ = v_isSharedCheck_4667_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4668_ = crate::leanh::lean_ctor_get(v___x_4659_, 0);
                    v_isSharedCheck_4675_ = (!crate::leanh::lean_is_exclusive(v___x_4659_)) as u8;
                    if v_isSharedCheck_4675_ == 0 {
                        v___x_4670_ = v___x_4659_;
                        v_isShared_4671_ = v_isSharedCheck_4675_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4668_);
                        crate::leanh::lean_dec(v___x_4659_);
                        v___x_4670_ = crate::leanh::lean_box(0);
                        v_isShared_4671_ = v_isSharedCheck_4675_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4663_ == 0 {
                    v___x_4665_ = v___x_4662_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4666_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
                    v___x_4665_ = v_reuseFailAlloc_4666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4665_;
            }
            3 => {
                if v_isShared_4671_ == 0 {
                    v___x_4673_ = v___x_4670_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
                    v___x_4673_ = v_reuseFailAlloc_4674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(
    mut v_e_4676_: *mut crate::leanh::LeanObject,
    mut v_k_4677_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4678_: *mut crate::leanh::LeanObject,
    mut v_preserveNondepLet_4679_: *mut crate::leanh::LeanObject,
    mut v_nondepLetOnly_4680_: *mut crate::leanh::LeanObject,
    mut v___y_4681_: *mut crate::leanh::LeanObject,
    mut v___y_4682_: *mut crate::leanh::LeanObject,
    mut v___y_4683_: *mut crate::leanh::LeanObject,
    mut v___y_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4686_: u8 = 0;
    let mut v_preserveNondepLet_boxed_4687_: u8 = 0;
    let mut v_nondepLetOnly_boxed_4688_: u8 = 0;
    let mut v_res_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4686_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4678_) as u8);
    v_preserveNondepLet_boxed_4687_ = (crate::leanh::lean_unbox(v_preserveNondepLet_4679_) as u8);
    v_nondepLetOnly_boxed_4688_ = (crate::leanh::lean_unbox(v_nondepLetOnly_4680_) as u8);
    v_res_4689_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(
        v_e_4676_,
        v_k_4677_,
        v_cleanupAnnotations_boxed_4686_,
        v_preserveNondepLet_boxed_4687_,
        v_nondepLetOnly_boxed_4688_,
        v___y_4681_,
        v___y_4682_,
        v___y_4683_,
        v___y_4684_,
    );
    crate::leanh::lean_dec(v___y_4684_);
    crate::leanh::lean_dec_ref(v___y_4683_);
    crate::leanh::lean_dec(v___y_4682_);
    crate::leanh::lean_dec_ref(v___y_4681_);
    return v_res_4689_;
}
pub unsafe fn l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(
    mut v_00_u03b1_4690_: *mut crate::leanh::LeanObject,
    mut v_e_4691_: *mut crate::leanh::LeanObject,
    mut v_k_4692_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4693_: u8,
    mut v_preserveNondepLet_4694_: u8,
    mut v_nondepLetOnly_4695_: u8,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
    mut v___y_4699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4701_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(
        v_e_4691_,
        v_k_4692_,
        v_cleanupAnnotations_4693_,
        v_preserveNondepLet_4694_,
        v_nondepLetOnly_4695_,
        v___y_4696_,
        v___y_4697_,
        v___y_4698_,
        v___y_4699_,
    );
    return v___x_4701_;
}
pub unsafe fn l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(
    mut v_00_u03b1_4702_: *mut crate::leanh::LeanObject,
    mut v_e_4703_: *mut crate::leanh::LeanObject,
    mut v_k_4704_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4705_: *mut crate::leanh::LeanObject,
    mut v_preserveNondepLet_4706_: *mut crate::leanh::LeanObject,
    mut v_nondepLetOnly_4707_: *mut crate::leanh::LeanObject,
    mut v___y_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
    mut v___y_4712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4713_: u8 = 0;
    let mut v_preserveNondepLet_boxed_4714_: u8 = 0;
    let mut v_nondepLetOnly_boxed_4715_: u8 = 0;
    let mut v_res_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4713_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4705_) as u8);
    v_preserveNondepLet_boxed_4714_ = (crate::leanh::lean_unbox(v_preserveNondepLet_4706_) as u8);
    v_nondepLetOnly_boxed_4715_ = (crate::leanh::lean_unbox(v_nondepLetOnly_4707_) as u8);
    v_res_4716_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(
        v_00_u03b1_4702_,
        v_e_4703_,
        v_k_4704_,
        v_cleanupAnnotations_boxed_4713_,
        v_preserveNondepLet_boxed_4714_,
        v_nondepLetOnly_boxed_4715_,
        v___y_4708_,
        v___y_4709_,
        v___y_4710_,
        v___y_4711_,
    );
    crate::leanh::lean_dec(v___y_4711_);
    crate::leanh::lean_dec_ref(v___y_4710_);
    crate::leanh::lean_dec(v___y_4709_);
    crate::leanh::lean_dec_ref(v___y_4708_);
    return v_res_4716_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(
    mut v_xs_4717_: *mut crate::leanh::LeanObject,
    mut v_a_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v_fst_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4732_: u8 = 0;
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: u8 = 0;
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: u8 = 0;
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4773_: u8 = 0;
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4777_: u8 = 0;
    let mut v_isSharedCheck_4778_: u8 = 0;
    let mut v_isSharedCheck_4779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4723_ = crate::leanh::lean_ctor_get(v_a_4718_, 1);
                v_fst_4724_ = crate::leanh::lean_ctor_get(v_a_4718_, 0);
                v_isSharedCheck_4779_ = (!crate::leanh::lean_is_exclusive(v_a_4718_)) as u8;
                if v_isSharedCheck_4779_ == 0 {
                    v___x_4726_ = v_a_4718_;
                    v_isShared_4727_ = v_isSharedCheck_4779_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4723_);
                    crate::leanh::lean_inc(v_fst_4724_);
                    crate::leanh::lean_dec(v_a_4718_);
                    v___x_4726_ = crate::leanh::lean_box(0);
                    v_isShared_4727_ = v_isSharedCheck_4779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_4728_ = crate::leanh::lean_ctor_get(v_snd_4723_, 0);
                v_snd_4729_ = crate::leanh::lean_ctor_get(v_snd_4723_, 1);
                v_isSharedCheck_4778_ = (!crate::leanh::lean_is_exclusive(v_snd_4723_)) as u8;
                if v_isSharedCheck_4778_ == 0 {
                    v___x_4731_ = v_snd_4723_;
                    v_isShared_4732_ = v_isSharedCheck_4778_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4729_);
                    crate::leanh::lean_inc(v_fst_4728_);
                    crate::leanh::lean_dec(v_snd_4723_);
                    v___x_4731_ = crate::leanh::lean_box(0);
                    v_isShared_4732_ = v_isSharedCheck_4778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4733_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4734_ = lean_nat_dec_lt(v___x_4733_, v_snd_4729_);
                if v___x_4734_ == 0 {
                    if v_isShared_4732_ == 0 {
                        v___x_4736_ = v___x_4731_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4741_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_fst_4728_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4741_, 1, v_snd_4729_);
                        v___x_4736_ = v_reuseFailAlloc_4741_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_fvarSet_4742_ = crate::leanh::lean_ctor_get(v_fst_4724_, 1);
                    v___x_4743_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4744_ = lean_nat_sub(v_snd_4729_, v___x_4743_);
                    crate::leanh::lean_dec(v_snd_4729_);
                    v___x_4745_ = l_Lean_instInhabitedExpr;
                    v___x_4746_ = lean_array_get_borrowed(v___x_4745_, v_xs_4717_, v___x_4744_);
                    v___x_4747_ = l_Lean_Expr_fvarId_x21(v___x_4746_);
                    v___x_4748_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_4747_, v_fvarSet_4742_);
                    if v___x_4748_ == 0 {
                        crate::leanh::lean_dec(v___x_4747_);
                        if v_isShared_4732_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4731_, 1, v___x_4744_);
                            v___x_4750_ = v___x_4731_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4755_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_fst_4728_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4755_, 1, v___x_4744_);
                            v___x_4750_ = v_reuseFailAlloc_4755_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_4756_ = l_Lean_FVarId_getDecl___redArg(
                            v___x_4747_,
                            v___y_4719_,
                            v___y_4720_,
                            v___y_4721_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4756_) == 0 {
                            v_a_4757_ = crate::leanh::lean_ctor_get(v___x_4756_, 0);
                            crate::leanh::lean_inc(v_a_4757_);
                            crate::leanh::lean_dec_ref_known(v___x_4756_, 1);
                            v___x_4758_ = l_Lean_LocalDecl_type(v_a_4757_);
                            v___x_4759_ = l_Lean_collectFVars(v_fst_4724_, v___x_4758_);
                            v___x_4760_ = l_Lean_LocalDecl_value(v_a_4757_, v___x_4748_);
                            crate::leanh::lean_dec(v_a_4757_);
                            v___x_4761_ = l_Lean_collectFVars(v___x_4759_, v___x_4760_);
                            crate::leanh::lean_inc(v___x_4746_);
                            v___x_4762_ = lean_array_push(v_fst_4728_, v___x_4746_);
                            if v_isShared_4732_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4731_, 1, v___x_4744_);
                                crate::leanh::lean_ctor_set(v___x_4731_, 0, v___x_4762_);
                                v___x_4764_ = v___x_4731_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_4769_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4762_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4769_, 1, v___x_4744_);
                                v___x_4764_ = v_reuseFailAlloc_4769_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_4744_);
                            crate::leanh::lean_del_object(v___x_4731_);
                            crate::leanh::lean_dec(v_fst_4728_);
                            crate::leanh::lean_del_object(v___x_4726_);
                            crate::leanh::lean_dec(v_fst_4724_);
                            v_a_4770_ = crate::leanh::lean_ctor_get(v___x_4756_, 0);
                            v_isSharedCheck_4777_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4756_)) as u8;
                            if v_isSharedCheck_4777_ == 0 {
                                v___x_4772_ = v___x_4756_;
                                v_isShared_4773_ = v_isSharedCheck_4777_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4770_);
                                crate::leanh::lean_dec(v___x_4756_);
                                v___x_4772_ = crate::leanh::lean_box(0);
                                v_isShared_4773_ = v_isSharedCheck_4777_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_4727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4726_, 1, v___x_4736_);
                    v___x_4738_ = v___x_4726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4740_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_fst_4724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 1, v___x_4736_);
                    v___x_4738_ = v_reuseFailAlloc_4740_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4739_, 0, v___x_4738_);
                return v___x_4739_;
            }
            5 => {
                if v_isShared_4727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4726_, 1, v___x_4750_);
                    v___x_4752_ = v___x_4726_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4754_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_fst_4724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4754_, 1, v___x_4750_);
                    v___x_4752_ = v_reuseFailAlloc_4754_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_4718_ = v___x_4752_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_4727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4726_, 1, v___x_4764_);
                    crate::leanh::lean_ctor_set(v___x_4726_, 0, v___x_4761_);
                    v___x_4766_ = v___x_4726_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4768_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4768_, 1, v___x_4764_);
                    v___x_4766_ = v_reuseFailAlloc_4768_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_4718_ = v___x_4766_;
                state = 0;
                continue;
            }
            9 => {
                if v_isShared_4773_ == 0 {
                    v___x_4775_ = v___x_4772_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4776_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
                    v___x_4775_ = v_reuseFailAlloc_4776_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(
    mut v_xs_4780_: *mut crate::leanh::LeanObject,
    mut v_a_4781_: *mut crate::leanh::LeanObject,
    mut v___y_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
    mut v___y_4785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4786_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(
            v_xs_4780_,
            v_a_4781_,
            v___y_4782_,
            v___y_4783_,
            v___y_4784_,
        );
    crate::leanh::lean_dec(v___y_4784_);
    crate::leanh::lean_dec_ref(v___y_4783_);
    crate::leanh::lean_dec_ref(v___y_4782_);
    crate::leanh::lean_dec_ref(v_xs_4780_);
    return v_res_4786_;
}
pub unsafe fn l_Lean_Meta_zetaUnused___lam__0(
    mut v___x_4787_: *mut crate::leanh::LeanObject,
    mut v_e_4788_: *mut crate::leanh::LeanObject,
    mut v_xs_4789_: *mut crate::leanh::LeanObject,
    mut v_body_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4807_: u8 = 0;
    let mut v_snd_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: u8 = 0;
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: u8 = 0;
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4819_: u8 = 0;
    let mut v_a_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4823_: u8 = 0;
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once), _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
                v___x_4797_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2;
                v___x_4798_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4798_, 0, v___x_4796_);
                crate::leanh::lean_ctor_set(v___x_4798_, 1, v___x_4787_);
                crate::leanh::lean_ctor_set(v___x_4798_, 2, v___x_4797_);
                crate::leanh::lean_inc_ref(v_body_4790_);
                v_s_4799_ = l_Lean_collectFVars(v___x_4798_, v_body_4790_);
                v_i_4800_ = lean_array_get_size(v_xs_4789_);
                v___x_4801_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4801_, 0, v___x_4797_);
                crate::leanh::lean_ctor_set(v___x_4801_, 1, v_i_4800_);
                v___x_4802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4802_, 0, v_s_4799_);
                crate::leanh::lean_ctor_set(v___x_4802_, 1, v___x_4801_);
                v___x_4803_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_4789_, v___x_4802_, v___y_4791_, v___y_4793_, v___y_4794_);
                if crate::leanh::lean_obj_tag(v___x_4803_) == 0 {
                    v_a_4804_ = crate::leanh::lean_ctor_get(v___x_4803_, 0);
                    v_isSharedCheck_4819_ = (!crate::leanh::lean_is_exclusive(v___x_4803_)) as u8;
                    if v_isSharedCheck_4819_ == 0 {
                        v___x_4806_ = v___x_4803_;
                        v_isShared_4807_ = v_isSharedCheck_4819_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4804_);
                        crate::leanh::lean_dec(v___x_4803_);
                        v___x_4806_ = crate::leanh::lean_box(0);
                        v_isShared_4807_ = v_isSharedCheck_4819_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_body_4790_);
                    crate::leanh::lean_dec_ref(v_e_4788_);
                    v_a_4820_ = crate::leanh::lean_ctor_get(v___x_4803_, 0);
                    v_isSharedCheck_4827_ = (!crate::leanh::lean_is_exclusive(v___x_4803_)) as u8;
                    if v_isSharedCheck_4827_ == 0 {
                        v___x_4822_ = v___x_4803_;
                        v_isShared_4823_ = v_isSharedCheck_4827_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4820_);
                        crate::leanh::lean_dec(v___x_4803_);
                        v___x_4822_ = crate::leanh::lean_box(0);
                        v_isShared_4823_ = v_isSharedCheck_4827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4808_ = crate::leanh::lean_ctor_get(v_a_4804_, 1);
                crate::leanh::lean_inc(v_snd_4808_);
                crate::leanh::lean_dec(v_a_4804_);
                v_fst_4809_ = crate::leanh::lean_ctor_get(v_snd_4808_, 0);
                crate::leanh::lean_inc(v_fst_4809_);
                crate::leanh::lean_dec(v_snd_4808_);
                v___x_4810_ = lean_array_get_size(v_fst_4809_);
                v___x_4811_ = lean_nat_dec_eq(v___x_4810_, v_i_4800_);
                if v___x_4811_ == 0 {
                    crate::leanh::lean_del_object(v___x_4806_);
                    crate::leanh::lean_dec_ref(v_e_4788_);
                    v___x_4812_ = 1;
                    v___x_4813_ = l_Array_reverse___redArg(v_fst_4809_);
                    v___x_4814_ = 1;
                    v___x_4815_ = l_Lean_Meta_mkLetFVars(
                        v___x_4813_,
                        v_body_4790_,
                        v___x_4812_,
                        v___x_4811_,
                        v___x_4814_,
                        v___y_4791_,
                        v___y_4792_,
                        v___y_4793_,
                        v___y_4794_,
                    );
                    crate::leanh::lean_dec_ref(v___x_4813_);
                    return v___x_4815_;
                } else {
                    crate::leanh::lean_dec(v_fst_4809_);
                    crate::leanh::lean_dec_ref(v_body_4790_);
                    if v_isShared_4807_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4806_, 0, v_e_4788_);
                        v___x_4817_ = v___x_4806_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_e_4788_);
                        v___x_4817_ = v_reuseFailAlloc_4818_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4817_;
            }
            3 => {
                if v_isShared_4823_ == 0 {
                    v___x_4825_ = v___x_4822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4826_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
                    v___x_4825_ = v_reuseFailAlloc_4826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_zetaUnused___lam__0___boxed(
    mut v___x_4828_: *mut crate::leanh::LeanObject,
    mut v_e_4829_: *mut crate::leanh::LeanObject,
    mut v_xs_4830_: *mut crate::leanh::LeanObject,
    mut v_body_4831_: *mut crate::leanh::LeanObject,
    mut v___y_4832_: *mut crate::leanh::LeanObject,
    mut v___y_4833_: *mut crate::leanh::LeanObject,
    mut v___y_4834_: *mut crate::leanh::LeanObject,
    mut v___y_4835_: *mut crate::leanh::LeanObject,
    mut v___y_4836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4837_ = l_Lean_Meta_zetaUnused___lam__0(
        v___x_4828_,
        v_e_4829_,
        v_xs_4830_,
        v_body_4831_,
        v___y_4832_,
        v___y_4833_,
        v___y_4834_,
        v___y_4835_,
    );
    crate::leanh::lean_dec(v___y_4835_);
    crate::leanh::lean_dec_ref(v___y_4834_);
    crate::leanh::lean_dec(v___y_4833_);
    crate::leanh::lean_dec_ref(v___y_4832_);
    crate::leanh::lean_dec_ref(v_xs_4830_);
    return v_res_4837_;
}
pub unsafe fn l_Lean_Meta_zetaUnused(
    mut v_e_4838_: *mut crate::leanh::LeanObject,
    mut v_a_4839_: *mut crate::leanh::LeanObject,
    mut v_a_4840_: *mut crate::leanh::LeanObject,
    mut v_a_4841_: *mut crate::leanh::LeanObject,
    mut v_a_4842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: u8 = 0;
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4844_ = crate::leanh::lean_box(1);
    crate::leanh::lean_inc_ref(v_e_4838_);
    v___f_4845_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_zetaUnused___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4845_, 0, v___x_4844_);
    crate::leanh::lean_closure_set(v___f_4845_, 1, v_e_4838_);
    v___x_4846_ = 0;
    v___x_4847_ = 1;
    v___x_4848_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(
        v_e_4838_,
        v___f_4845_,
        v___x_4846_,
        v___x_4847_,
        v___x_4846_,
        v_a_4839_,
        v_a_4840_,
        v_a_4841_,
        v_a_4842_,
    );
    return v___x_4848_;
}
pub unsafe fn l_Lean_Meta_zetaUnused___boxed(
    mut v_e_4849_: *mut crate::leanh::LeanObject,
    mut v_a_4850_: *mut crate::leanh::LeanObject,
    mut v_a_4851_: *mut crate::leanh::LeanObject,
    mut v_a_4852_: *mut crate::leanh::LeanObject,
    mut v_a_4853_: *mut crate::leanh::LeanObject,
    mut v_a_4854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4855_ = l_Lean_Meta_zetaUnused(v_e_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
    crate::leanh::lean_dec(v_a_4853_);
    crate::leanh::lean_dec_ref(v_a_4852_);
    crate::leanh::lean_dec(v_a_4851_);
    crate::leanh::lean_dec_ref(v_a_4850_);
    return v_res_4855_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0(
    mut v_xs_4856_: *mut crate::leanh::LeanObject,
    mut v_inst_4857_: *mut crate::leanh::LeanObject,
    mut v_a_4858_: *mut crate::leanh::LeanObject,
    mut v___y_4859_: *mut crate::leanh::LeanObject,
    mut v___y_4860_: *mut crate::leanh::LeanObject,
    mut v___y_4861_: *mut crate::leanh::LeanObject,
    mut v___y_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4864_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(
            v_xs_4856_,
            v_a_4858_,
            v___y_4859_,
            v___y_4861_,
            v___y_4862_,
        );
    return v___x_4864_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(
    mut v_xs_4865_: *mut crate::leanh::LeanObject,
    mut v_inst_4866_: *mut crate::leanh::LeanObject,
    mut v_a_4867_: *mut crate::leanh::LeanObject,
    mut v___y_4868_: *mut crate::leanh::LeanObject,
    mut v___y_4869_: *mut crate::leanh::LeanObject,
    mut v___y_4870_: *mut crate::leanh::LeanObject,
    mut v___y_4871_: *mut crate::leanh::LeanObject,
    mut v___y_4872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4873_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0(
        v_xs_4865_,
        v_inst_4866_,
        v_a_4867_,
        v___y_4868_,
        v___y_4869_,
        v___y_4870_,
        v___y_4871_,
    );
    crate::leanh::lean_dec(v___y_4871_);
    crate::leanh::lean_dec_ref(v___y_4870_);
    crate::leanh::lean_dec(v___y_4869_);
    crate::leanh::lean_dec_ref(v___y_4868_);
    crate::leanh::lean_dec_ref(v_xs_4865_);
    return v_res_4873_;
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(
    mut v_u_4878_: *mut crate::leanh::LeanObject,
    mut v_source_4879_: *mut crate::leanh::LeanObject,
    mut v_result_4880_: *mut crate::leanh::LeanObject,
    mut v_keepUnused_4881_: u8,
    mut v_a_4882_: *mut crate::leanh::LeanObject,
    mut v_a_4883_: *mut crate::leanh::LeanObject,
    mut v_a_4884_: *mut crate::leanh::LeanObject,
    mut v_a_4885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modified_4887_: u8 = 0;
    let mut v_exprType_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4893_: u8 = 0;
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut v_a_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4912_: u8 = 0;
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4916_: u8 = 0;
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprType_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprInit_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprResult_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v___x_4937_: u8 = 0;
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4952_: u8 = 0;
    let mut v_a_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4956_: u8 = 0;
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4960_: u8 = 0;
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_modified_4887_ = crate::leanh::lean_ctor_get_uint8(
                    v_result_4880_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                );
                if v_modified_4887_ == 0 {
                    if v_keepUnused_4881_ == 0 {
                        v_exprType_4888_ = crate::leanh::lean_ctor_get(v_result_4880_, 1);
                        crate::leanh::lean_inc_ref(v_exprType_4888_);
                        crate::leanh::lean_dec_ref(v_result_4880_);
                        crate::leanh::lean_inc_ref(v_source_4879_);
                        v___x_4889_ = l_Lean_Meta_zetaUnused(
                            v_source_4879_,
                            v_a_4882_,
                            v_a_4883_,
                            v_a_4884_,
                            v_a_4885_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4889_) == 0 {
                            v_a_4890_ = crate::leanh::lean_ctor_get(v___x_4889_, 0);
                            v_isSharedCheck_4908_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4889_)) as u8;
                            if v_isSharedCheck_4908_ == 0 {
                                v___x_4892_ = v___x_4889_;
                                v_isShared_4893_ = v_isSharedCheck_4908_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4890_);
                                crate::leanh::lean_dec(v___x_4889_);
                                v___x_4892_ = crate::leanh::lean_box(0);
                                v_isShared_4893_ = v_isSharedCheck_4908_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_exprType_4888_);
                            crate::leanh::lean_dec_ref(v_source_4879_);
                            crate::leanh::lean_dec(v_u_4878_);
                            v_a_4909_ = crate::leanh::lean_ctor_get(v___x_4889_, 0);
                            v_isSharedCheck_4916_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4889_)) as u8;
                            if v_isSharedCheck_4916_ == 0 {
                                v___x_4911_ = v___x_4889_;
                                v_isShared_4912_ = v_isSharedCheck_4916_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4909_);
                                crate::leanh::lean_dec(v___x_4889_);
                                v___x_4911_ = crate::leanh::lean_box(0);
                                v_isShared_4912_ = v_isSharedCheck_4916_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_result_4880_);
                        crate::leanh::lean_dec_ref(v_source_4879_);
                        crate::leanh::lean_dec(v_u_4878_);
                        v___x_4917_ = crate::leanh::lean_box(0);
                        v___x_4918_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4918_, 0, v___x_4917_);
                        return v___x_4918_;
                    }
                } else {
                    v_expr_4919_ = crate::leanh::lean_ctor_get(v_result_4880_, 0);
                    crate::leanh::lean_inc_ref(v_expr_4919_);
                    v_exprType_4920_ = crate::leanh::lean_ctor_get(v_result_4880_, 1);
                    crate::leanh::lean_inc_ref_n(v_exprType_4920_, 3);
                    v_exprInit_4921_ = crate::leanh::lean_ctor_get(v_result_4880_, 2);
                    crate::leanh::lean_inc_ref(v_exprInit_4921_);
                    v_exprResult_4922_ = crate::leanh::lean_ctor_get(v_result_4880_, 3);
                    crate::leanh::lean_inc_ref_n(v_exprResult_4922_, 2);
                    v_proof_4923_ = crate::leanh::lean_ctor_get(v_result_4880_, 4);
                    crate::leanh::lean_inc_ref(v_proof_4923_);
                    crate::leanh::lean_dec_ref(v_result_4880_);
                    v___x_4924_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5;
                    v___x_4925_ = crate::leanh::lean_box(0);
                    v___x_4926_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4926_, 0, v_u_4878_);
                    crate::leanh::lean_ctor_set(v___x_4926_, 1, v___x_4925_);
                    crate::leanh::lean_inc_ref(v___x_4926_);
                    v___x_4927_ = l_Lean_mkConst(v___x_4924_, v___x_4926_);
                    crate::leanh::lean_inc_ref(v___x_4927_);
                    v___x_4928_ = l_Lean_mkApp3(
                        v___x_4927_,
                        v_exprType_4920_,
                        v_exprInit_4921_,
                        v_expr_4919_,
                    );
                    v___x_4929_ = l_Lean_Meta_mkExpectedPropHint(v_proof_4923_, v___x_4928_);
                    crate::leanh::lean_inc_ref(v_source_4879_);
                    v___x_4930_ = l_Lean_mkApp3(
                        v___x_4927_,
                        v_exprType_4920_,
                        v_source_4879_,
                        v_exprResult_4922_,
                    );
                    v_proof_4931_ = l_Lean_Meta_mkExpectedPropHint(v___x_4929_, v___x_4930_);
                    if v_keepUnused_4881_ == 0 {
                        crate::leanh::lean_inc_ref(v_exprResult_4922_);
                        v___x_4932_ = l_Lean_Meta_zetaUnused(
                            v_exprResult_4922_,
                            v_a_4882_,
                            v_a_4883_,
                            v_a_4884_,
                            v_a_4885_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4932_) == 0 {
                            v_a_4933_ = crate::leanh::lean_ctor_get(v___x_4932_, 0);
                            v_isSharedCheck_4952_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4932_)) as u8;
                            if v_isSharedCheck_4952_ == 0 {
                                v___x_4935_ = v___x_4932_;
                                v_isShared_4936_ = v_isSharedCheck_4952_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4933_);
                                crate::leanh::lean_dec(v___x_4932_);
                                v___x_4935_ = crate::leanh::lean_box(0);
                                v_isShared_4936_ = v_isSharedCheck_4952_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_proof_4931_);
                            crate::leanh::lean_dec_ref_known(v___x_4926_, 2);
                            crate::leanh::lean_dec_ref(v_exprResult_4922_);
                            crate::leanh::lean_dec_ref(v_exprType_4920_);
                            crate::leanh::lean_dec_ref(v_source_4879_);
                            v_a_4953_ = crate::leanh::lean_ctor_get(v___x_4932_, 0);
                            v_isSharedCheck_4960_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4932_)) as u8;
                            if v_isSharedCheck_4960_ == 0 {
                                v___x_4955_ = v___x_4932_;
                                v_isShared_4956_ = v_isSharedCheck_4960_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4953_);
                                crate::leanh::lean_dec(v___x_4932_);
                                v___x_4955_ = crate::leanh::lean_box(0);
                                v_isShared_4956_ = v_isSharedCheck_4960_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4926_, 2);
                        crate::leanh::lean_dec_ref(v_exprType_4920_);
                        crate::leanh::lean_dec_ref(v_source_4879_);
                        v___x_4961_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4961_, 0, v_exprResult_4922_);
                        crate::leanh::lean_ctor_set(v___x_4961_, 1, v_proof_4931_);
                        v___x_4962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4962_, 0, v___x_4961_);
                        return v___x_4962_;
                    }
                }
            }
            1 => {
                v___x_4894_ = lean_expr_eqv(v_a_4890_, v_source_4879_);
                crate::leanh::lean_dec_ref(v_source_4879_);
                if v___x_4894_ == 0 {
                    v___x_4895_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2;
                    v___x_4896_ = crate::leanh::lean_box(0);
                    v___x_4897_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4897_, 0, v_u_4878_);
                    crate::leanh::lean_ctor_set(v___x_4897_, 1, v___x_4896_);
                    v___x_4898_ = l_Lean_mkConst(v___x_4895_, v___x_4897_);
                    crate::leanh::lean_inc(v_a_4890_);
                    v___x_4899_ = l_Lean_mkAppB(v___x_4898_, v_exprType_4888_, v_a_4890_);
                    v___x_4900_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4900_, 0, v_a_4890_);
                    crate::leanh::lean_ctor_set(v___x_4900_, 1, v___x_4899_);
                    if v_isShared_4893_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4892_, 0, v___x_4900_);
                        v___x_4902_ = v___x_4892_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4900_);
                        v___x_4902_ = v_reuseFailAlloc_4903_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4890_);
                    crate::leanh::lean_dec_ref(v_exprType_4888_);
                    crate::leanh::lean_dec(v_u_4878_);
                    v___x_4904_ = crate::leanh::lean_box(0);
                    if v_isShared_4893_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4892_, 0, v___x_4904_);
                        v___x_4906_ = v___x_4892_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 0, v___x_4904_);
                        v___x_4906_ = v_reuseFailAlloc_4907_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4902_;
            }
            3 => {
                return v___x_4906_;
            }
            4 => {
                if v_isShared_4912_ == 0 {
                    v___x_4914_ = v___x_4911_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4915_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
                    v___x_4914_ = v_reuseFailAlloc_4915_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4914_;
            }
            6 => {
                v___x_4937_ = lean_expr_eqv(v_a_4933_, v_exprResult_4922_);
                if v___x_4937_ == 0 {
                    v___x_4938_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1;
                    crate::leanh::lean_inc_ref(v___x_4926_);
                    v___x_4939_ = l_Lean_mkConst(v___x_4938_, v___x_4926_);
                    v___x_4940_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2;
                    v___x_4941_ = l_Lean_mkConst(v___x_4940_, v___x_4926_);
                    crate::leanh::lean_inc_n(v_a_4933_, 2);
                    crate::leanh::lean_inc_ref(v_exprType_4920_);
                    v___x_4942_ = l_Lean_mkAppB(v___x_4941_, v_exprType_4920_, v_a_4933_);
                    v___x_4943_ = l_Lean_mkApp6(
                        v___x_4939_,
                        v_exprType_4920_,
                        v_source_4879_,
                        v_exprResult_4922_,
                        v_a_4933_,
                        v_proof_4931_,
                        v___x_4942_,
                    );
                    v___x_4944_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4944_, 0, v_a_4933_);
                    crate::leanh::lean_ctor_set(v___x_4944_, 1, v___x_4943_);
                    if v_isShared_4936_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4935_, 0, v___x_4944_);
                        v___x_4946_ = v___x_4935_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4944_);
                        v___x_4946_ = v_reuseFailAlloc_4947_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4933_);
                    crate::leanh::lean_dec_ref_known(v___x_4926_, 2);
                    crate::leanh::lean_dec_ref(v_exprType_4920_);
                    crate::leanh::lean_dec_ref(v_source_4879_);
                    v___x_4948_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4948_, 0, v_exprResult_4922_);
                    crate::leanh::lean_ctor_set(v___x_4948_, 1, v_proof_4931_);
                    if v_isShared_4936_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4935_, 0, v___x_4948_);
                        v___x_4950_ = v___x_4935_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4948_);
                        v___x_4950_ = v_reuseFailAlloc_4951_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_4946_;
            }
            8 => {
                return v___x_4950_;
            }
            9 => {
                if v_isShared_4956_ == 0 {
                    v___x_4958_ = v___x_4955_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
                    v___x_4958_ = v_reuseFailAlloc_4959_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(
    mut v_u_4963_: *mut crate::leanh::LeanObject,
    mut v_source_4964_: *mut crate::leanh::LeanObject,
    mut v_result_4965_: *mut crate::leanh::LeanObject,
    mut v_keepUnused_4966_: *mut crate::leanh::LeanObject,
    mut v_a_4967_: *mut crate::leanh::LeanObject,
    mut v_a_4968_: *mut crate::leanh::LeanObject,
    mut v_a_4969_: *mut crate::leanh::LeanObject,
    mut v_a_4970_: *mut crate::leanh::LeanObject,
    mut v_a_4971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keepUnused_boxed_4972_: u8 = 0;
    let mut v_res_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keepUnused_boxed_4972_ = (crate::leanh::lean_unbox(v_keepUnused_4966_) as u8);
    v_res_4973_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(
        v_u_4963_,
        v_source_4964_,
        v_result_4965_,
        v_keepUnused_boxed_4972_,
        v_a_4967_,
        v_a_4968_,
        v_a_4969_,
        v_a_4970_,
    );
    crate::leanh::lean_dec(v_a_4970_);
    crate::leanh::lean_dec_ref(v_a_4969_);
    crate::leanh::lean_dec(v_a_4968_);
    crate::leanh::lean_dec_ref(v_a_4967_);
    return v_res_4973_;
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope___redArg___lam__0(
    mut v_level_4974_: *mut crate::leanh::LeanObject,
    mut v_e_4975_: *mut crate::leanh::LeanObject,
    mut v_inst_4976_: *mut crate::leanh::LeanObject,
    mut v_zetaUnusedMode_4977_: u8,
    mut v___x_4978_: u8,
    mut v___x_4979_: u8,
    mut v_r_4980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4982_: u8 = 0;
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_zetaUnusedMode_4977_ {
                0 => {
                    v___y_4982_ = v___x_4978_;
                    state = 1;
                    continue;
                }
                1 => {
                    v___y_4982_ = v___x_4978_;
                    state = 1;
                    continue;
                }
                _ => {
                    v___y_4982_ = v___x_4979_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_4983_ = crate::leanh::lean_box((v___y_4982_) as usize);
                v___x_4984_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_4984_, 0, v_level_4974_);
                crate::leanh::lean_closure_set(v___x_4984_, 1, v_e_4975_);
                crate::leanh::lean_closure_set(v___x_4984_, 2, v_r_4980_);
                crate::leanh::lean_closure_set(v___x_4984_, 3, v___x_4983_);
                v___x_4985_ = crate::leanh::lean_apply_2(
                    v_inst_4976_,
                    crate::leanh::lean_box(0),
                    v___x_4984_,
                );
                return v___x_4985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(
    mut v_level_4986_: *mut crate::leanh::LeanObject,
    mut v_e_4987_: *mut crate::leanh::LeanObject,
    mut v_inst_4988_: *mut crate::leanh::LeanObject,
    mut v_zetaUnusedMode_4989_: *mut crate::leanh::LeanObject,
    mut v___x_4990_: *mut crate::leanh::LeanObject,
    mut v___x_4991_: *mut crate::leanh::LeanObject,
    mut v_r_4992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zetaUnusedMode_boxed_4993_: u8 = 0;
    let mut v___x_363__boxed_4994_: u8 = 0;
    let mut v___x_364__boxed_4995_: u8 = 0;
    let mut v_res_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zetaUnusedMode_boxed_4993_ = (crate::leanh::lean_unbox(v_zetaUnusedMode_4989_) as u8);
    v___x_363__boxed_4994_ = (crate::leanh::lean_unbox(v___x_4990_) as u8);
    v___x_364__boxed_4995_ = (crate::leanh::lean_unbox(v___x_4991_) as u8);
    v_res_4996_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(
        v_level_4986_,
        v_e_4987_,
        v_inst_4988_,
        v_zetaUnusedMode_boxed_4993_,
        v___x_363__boxed_4994_,
        v___x_364__boxed_4995_,
        v_r_4992_,
    );
    return v_res_4996_;
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope___redArg___lam__1(
    mut v___x_4997_: *mut crate::leanh::LeanObject,
    mut v_inst_4998_: *mut crate::leanh::LeanObject,
    mut v_inst_4999_: *mut crate::leanh::LeanObject,
    mut v_inst_5000_: *mut crate::leanh::LeanObject,
    mut v_inst_5001_: *mut crate::leanh::LeanObject,
    mut v_info_5002_: *mut crate::leanh::LeanObject,
    mut v_e_5003_: *mut crate::leanh::LeanObject,
    mut v___x_5004_: *mut crate::leanh::LeanObject,
    mut v_toBind_5005_: *mut crate::leanh::LeanObject,
    mut v___f_5006_: *mut crate::leanh::LeanObject,
    mut v_____x_5007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_5008_ = crate::leanh::lean_ctor_get(v_____x_5007_, 0);
    crate::leanh::lean_inc(v_fst_5008_);
    v_snd_5009_ = crate::leanh::lean_ctor_get(v_____x_5007_, 1);
    crate::leanh::lean_inc(v_snd_5009_);
    crate::leanh::lean_dec_ref(v_____x_5007_);
    v___x_5010_ = lean_mk_empty_array_with_capacity(v___x_4997_);
    v___x_5011_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(
        v_inst_4998_,
        v_inst_4999_,
        v_inst_5000_,
        v_inst_5001_,
        v_info_5002_,
        v_fst_5008_,
        v_snd_5009_,
        v_e_5003_,
        v___x_5004_,
        v___x_5010_,
    );
    v___x_5012_ = crate::leanh::lean_apply_4(
        v_toBind_5005_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5011_,
        v___f_5006_,
    );
    return v___x_5012_;
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(
    mut v___x_5013_: *mut crate::leanh::LeanObject,
    mut v_inst_5014_: *mut crate::leanh::LeanObject,
    mut v_inst_5015_: *mut crate::leanh::LeanObject,
    mut v_inst_5016_: *mut crate::leanh::LeanObject,
    mut v_inst_5017_: *mut crate::leanh::LeanObject,
    mut v_info_5018_: *mut crate::leanh::LeanObject,
    mut v_e_5019_: *mut crate::leanh::LeanObject,
    mut v___x_5020_: *mut crate::leanh::LeanObject,
    mut v_toBind_5021_: *mut crate::leanh::LeanObject,
    mut v___f_5022_: *mut crate::leanh::LeanObject,
    mut v_____x_5023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5024_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(
        v___x_5013_,
        v_inst_5014_,
        v_inst_5015_,
        v_inst_5016_,
        v_inst_5017_,
        v_info_5018_,
        v_e_5019_,
        v___x_5020_,
        v_toBind_5021_,
        v___f_5022_,
        v_____x_5023_,
    );
    crate::leanh::lean_dec(v___x_5013_);
    return v_res_5024_;
}
pub unsafe fn _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5027_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1;
    v___x_5028_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_5029_ = crate::leanh::lean_unsigned_to_nat(456);
    v___x_5030_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0;
    v___x_5031_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3;
    v___x_5032_ = l_mkPanicMessageWithDecl(
        v___x_5031_,
        v___x_5030_,
        v___x_5029_,
        v___x_5028_,
        v___x_5027_,
    );
    return v___x_5032_;
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope___redArg___lam__2(
    mut v_e_5033_: *mut crate::leanh::LeanObject,
    mut v_inst_5034_: *mut crate::leanh::LeanObject,
    mut v_zetaUnusedMode_5035_: u8,
    mut v_inst_5036_: *mut crate::leanh::LeanObject,
    mut v_inst_5037_: *mut crate::leanh::LeanObject,
    mut v_inst_5038_: *mut crate::leanh::LeanObject,
    mut v_toBind_5039_: *mut crate::leanh::LeanObject,
    mut v_info_5040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_haveInfo_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_level_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: u8 = 0;
    let mut v___x_5046_: u8 = 0;
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5053_: u8 = 0;
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_haveInfo_5041_ = crate::leanh::lean_ctor_get(v_info_5040_, 0);
                v_level_5042_ = crate::leanh::lean_ctor_get(v_info_5040_, 5);
                v___x_5043_ = lean_array_get_size(v_haveInfo_5041_);
                v___x_5044_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5045_ = lean_nat_dec_eq(v___x_5043_, v___x_5044_);
                if v___x_5045_ == 0 {
                    v___x_5046_ = 1;
                    v___x_5047_ = crate::leanh::lean_box((v_zetaUnusedMode_5035_) as usize);
                    v___x_5048_ = crate::leanh::lean_box((v___x_5046_) as usize);
                    v___x_5049_ = crate::leanh::lean_box((v___x_5045_) as usize);
                    crate::leanh::lean_inc_n(v_inst_5034_, 2);
                    crate::leanh::lean_inc_ref(v_e_5033_);
                    crate::leanh::lean_inc(v_level_5042_);
                    v___f_5050_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        7,
                        6,
                    );
                    crate::leanh::lean_closure_set(v___f_5050_, 0, v_level_5042_);
                    crate::leanh::lean_closure_set(v___f_5050_, 1, v_e_5033_);
                    crate::leanh::lean_closure_set(v___f_5050_, 2, v_inst_5034_);
                    crate::leanh::lean_closure_set(v___f_5050_, 3, v___x_5047_);
                    crate::leanh::lean_closure_set(v___f_5050_, 4, v___x_5048_);
                    crate::leanh::lean_closure_set(v___f_5050_, 5, v___x_5049_);
                    crate::leanh::lean_inc(v_toBind_5039_);
                    crate::leanh::lean_inc_ref(v_info_5040_);
                    v___f_5051_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        11,
                        10,
                    );
                    crate::leanh::lean_closure_set(v___f_5051_, 0, v___x_5043_);
                    crate::leanh::lean_closure_set(v___f_5051_, 1, v_inst_5036_);
                    crate::leanh::lean_closure_set(v___f_5051_, 2, v_inst_5034_);
                    crate::leanh::lean_closure_set(v___f_5051_, 3, v_inst_5037_);
                    crate::leanh::lean_closure_set(v___f_5051_, 4, v_inst_5038_);
                    crate::leanh::lean_closure_set(v___f_5051_, 5, v_info_5040_);
                    crate::leanh::lean_closure_set(v___f_5051_, 6, v_e_5033_);
                    crate::leanh::lean_closure_set(v___f_5051_, 7, v___x_5044_);
                    crate::leanh::lean_closure_set(v___f_5051_, 8, v_toBind_5039_);
                    crate::leanh::lean_closure_set(v___f_5051_, 9, v___f_5050_);
                    match v_zetaUnusedMode_5035_ {
                        0 => {
                            v___y_5053_ = v___x_5046_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v___y_5053_ = v___x_5046_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_5053_ = v___x_5045_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_5040_);
                    crate::leanh::lean_dec(v_toBind_5039_);
                    crate::leanh::lean_dec_ref(v_inst_5038_);
                    crate::leanh::lean_dec_ref(v_inst_5037_);
                    crate::leanh::lean_dec(v_inst_5034_);
                    crate::leanh::lean_dec_ref(v_e_5033_);
                    v___x_5058_ = crate::leanh::lean_box(0);
                    v___x_5059_ = l_instInhabitedOfMonad___redArg(v_inst_5036_, v___x_5058_);
                    v___x_5060_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once
                        ),
                        _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2,
                    );
                    v___x_5061_ = l_panic___redArg(v___x_5059_, v___x_5060_);
                    crate::leanh::lean_dec(v___x_5059_);
                    return v___x_5061_;
                }
            }
            1 => {
                v___x_5054_ = crate::leanh::lean_box((v___y_5053_) as usize);
                v___x_5055_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_5055_, 0, v_info_5040_);
                crate::leanh::lean_closure_set(v___x_5055_, 1, v___x_5054_);
                v___x_5056_ = crate::leanh::lean_apply_2(
                    v_inst_5034_,
                    crate::leanh::lean_box(0),
                    v___x_5055_,
                );
                v___x_5057_ = crate::leanh::lean_apply_4(
                    v_toBind_5039_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5056_,
                    v___f_5051_,
                );
                return v___x_5057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(
    mut v_e_5062_: *mut crate::leanh::LeanObject,
    mut v_inst_5063_: *mut crate::leanh::LeanObject,
    mut v_zetaUnusedMode_5064_: *mut crate::leanh::LeanObject,
    mut v_inst_5065_: *mut crate::leanh::LeanObject,
    mut v_inst_5066_: *mut crate::leanh::LeanObject,
    mut v_inst_5067_: *mut crate::leanh::LeanObject,
    mut v_toBind_5068_: *mut crate::leanh::LeanObject,
    mut v_info_5069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zetaUnusedMode_boxed_5070_: u8 = 0;
    let mut v_res_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zetaUnusedMode_boxed_5070_ = (crate::leanh::lean_unbox(v_zetaUnusedMode_5064_) as u8);
    v_res_5071_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(
        v_e_5062_,
        v_inst_5063_,
        v_zetaUnusedMode_boxed_5070_,
        v_inst_5065_,
        v_inst_5066_,
        v_inst_5067_,
        v_toBind_5068_,
        v_info_5069_,
    );
    return v_res_5071_;
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope___redArg(
    mut v_inst_5072_: *mut crate::leanh::LeanObject,
    mut v_inst_5073_: *mut crate::leanh::LeanObject,
    mut v_inst_5074_: *mut crate::leanh::LeanObject,
    mut v_inst_5075_: *mut crate::leanh::LeanObject,
    mut v_e_5076_: *mut crate::leanh::LeanObject,
    mut v_zetaUnusedMode_5077_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_5078_ = crate::leanh::lean_ctor_get(v_inst_5072_, 1);
    crate::leanh::lean_inc_n(v_toBind_5078_, 2);
    v___x_5079_ = crate::leanh::lean_box((v_zetaUnusedMode_5077_) as usize);
    crate::leanh::lean_inc(v_inst_5073_);
    crate::leanh::lean_inc_ref(v_e_5076_);
    v___f_5080_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_5080_, 0, v_e_5076_);
    crate::leanh::lean_closure_set(v___f_5080_, 1, v_inst_5073_);
    crate::leanh::lean_closure_set(v___f_5080_, 2, v___x_5079_);
    crate::leanh::lean_closure_set(v___f_5080_, 3, v_inst_5072_);
    crate::leanh::lean_closure_set(v___f_5080_, 4, v_inst_5074_);
    crate::leanh::lean_closure_set(v___f_5080_, 5, v_inst_5075_);
    crate::leanh::lean_closure_set(v___f_5080_, 6, v_toBind_5078_);
    v___x_5081_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_getHaveTelescopeInfo___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_5081_, 0, v_e_5076_);
    v___x_5082_ = crate::leanh::lean_apply_2(v_inst_5073_, crate::leanh::lean_box(0), v___x_5081_);
    v___x_5083_ = crate::leanh::lean_apply_4(
        v_toBind_5078_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5082_,
        v___f_5080_,
    );
    return v___x_5083_;
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope___redArg___boxed(
    mut v_inst_5084_: *mut crate::leanh::LeanObject,
    mut v_inst_5085_: *mut crate::leanh::LeanObject,
    mut v_inst_5086_: *mut crate::leanh::LeanObject,
    mut v_inst_5087_: *mut crate::leanh::LeanObject,
    mut v_e_5088_: *mut crate::leanh::LeanObject,
    mut v_zetaUnusedMode_5089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zetaUnusedMode_boxed_5090_: u8 = 0;
    let mut v_res_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zetaUnusedMode_boxed_5090_ = (crate::leanh::lean_unbox(v_zetaUnusedMode_5089_) as u8);
    v_res_5091_ = l_Lean_Meta_simpHaveTelescope___redArg(
        v_inst_5084_,
        v_inst_5085_,
        v_inst_5086_,
        v_inst_5087_,
        v_e_5088_,
        v_zetaUnusedMode_boxed_5090_,
    );
    return v_res_5091_;
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope(
    mut v_m_5092_: *mut crate::leanh::LeanObject,
    mut v_inst_5093_: *mut crate::leanh::LeanObject,
    mut v_inst_5094_: *mut crate::leanh::LeanObject,
    mut v_inst_5095_: *mut crate::leanh::LeanObject,
    mut v_inst_5096_: *mut crate::leanh::LeanObject,
    mut v_e_5097_: *mut crate::leanh::LeanObject,
    mut v_zetaUnusedMode_5098_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5099_ = l_Lean_Meta_simpHaveTelescope___redArg(
        v_inst_5093_,
        v_inst_5094_,
        v_inst_5095_,
        v_inst_5096_,
        v_e_5097_,
        v_zetaUnusedMode_5098_,
    );
    return v___x_5099_;
}
pub unsafe fn l_Lean_Meta_simpHaveTelescope___boxed(
    mut v_m_5100_: *mut crate::leanh::LeanObject,
    mut v_inst_5101_: *mut crate::leanh::LeanObject,
    mut v_inst_5102_: *mut crate::leanh::LeanObject,
    mut v_inst_5103_: *mut crate::leanh::LeanObject,
    mut v_inst_5104_: *mut crate::leanh::LeanObject,
    mut v_e_5105_: *mut crate::leanh::LeanObject,
    mut v_zetaUnusedMode_5106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zetaUnusedMode_boxed_5107_: u8 = 0;
    let mut v_res_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zetaUnusedMode_boxed_5107_ = (crate::leanh::lean_unbox(v_zetaUnusedMode_5106_) as u8);
    v_res_5108_ = l_Lean_Meta_simpHaveTelescope(
        v_m_5100_,
        v_inst_5101_,
        v_inst_5102_,
        v_inst_5103_,
        v_inst_5104_,
        v_e_5105_,
        v_zetaUnusedMode_boxed_5107_,
    );
    return v_res_5108_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_HaveTelescope(
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
    res = runtime_initialize_Lean_Meta_MonadSimp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLooseBVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_instInhabitedHaveInfo_default = _init_l_Lean_Meta_instInhabitedHaveInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedHaveInfo_default);
    l_Lean_Meta_instInhabitedHaveInfo = _init_l_Lean_Meta_instInhabitedHaveInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedHaveInfo);
    l_Lean_Meta_instInhabitedHaveTelescopeInfo_default =
        _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default);
    l_Lean_Meta_instInhabitedHaveTelescopeInfo = _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedHaveTelescopeInfo);
    l_Lean_Meta_instInhabitedSimpHaveResult_default =
        _init_l_Lean_Meta_instInhabitedSimpHaveResult_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedSimpHaveResult_default);
    l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult =
        _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_HaveTelescope(
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
pub unsafe fn initialize_Lean_Meta_HaveTelescope(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Meta_MonadSimp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLooseBVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HaveTelescope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_HaveTelescope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_HaveTelescope(builtin);
}
