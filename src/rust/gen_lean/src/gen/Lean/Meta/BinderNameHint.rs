// Lean compiler output
// Module: Lean.Meta.BinderNameHint
// Imports: Lean.Meta.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_pop, lean_array_push, lean_array_set, lean_array_uget_borrowed, lean_array_uset,
    lean_find_expr, lean_mk_array, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed, lean_ptr_addr, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
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
    l_Lean_Core_instInhabitedCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed, l_Lean_Core_mkFreshUserName,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_forallE___override, l_Lean_Expr_headBeta, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_isConstOf, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_ExprStructEq_beq,
    l_Lean_ExprStructEq_beq___boxed, l_Lean_ExprStructEq_hash, l_Lean_ExprStructEq_hash___boxed,
    l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Util::MonadCache::l_Lean_MonadCacheT_instMonad___redArg;
pub static l_Lean_Expr_hasBinderNameHint___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        98, 105, 110, 100, 101, 114, 78, 97, 109, 101, 72, 105, 110, 116, 0,
    ],
};
static mut l_Lean_Expr_hasBinderNameHint___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_hasBinderNameHint___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_hasBinderNameHint___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Expr_hasBinderNameHint___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11058976731835024691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Expr_hasBinderNameHint___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_hasBinderNameHint___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_hasBinderNameHint___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_hasBinderNameHint___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Expr_hasBinderNameHint___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_hasBinderNameHint___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 66, 105, 110, 100, 101, 114, 78, 97, 109, 101,
        72, 105, 110, 116, 0,
    ],
};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__1_value:
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
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 66,
        105, 110, 100, 101, 114, 78, 97, 109, 101, 72, 105, 110, 116, 46, 48, 46, 76, 101, 97, 110,
        46, 101, 120, 105, 116, 83, 99, 111, 112, 101, 0,
    ],
};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__2_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 120, 115, 46, 115, 105, 122, 101, 32, 62, 32, 48, 10, 32, 32, 32, 32, 0,
    ],
};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__0_value:
    crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 66,
        105, 110, 100, 101, 114, 78, 97, 109, 101, 72, 105, 110, 116, 46, 48, 46, 76, 101, 97, 110,
        46, 114, 101, 109, 101, 109, 98, 101, 114, 78, 97, 109, 101, 0,
    ],
};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 120, 115, 46, 115, 105, 122, 101, 32, 62, 32, 98, 105, 100, 120, 10, 32, 32, 32,
        32, 0,
    ],
};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__0_value:
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
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 66,
        105, 110, 100, 101, 114, 78, 97, 109, 101, 72, 105, 110, 116, 46, 48, 46, 76, 101, 97, 110,
        46, 109, 97, 107, 101, 70, 114, 101, 115, 104, 0,
    ],
};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_ExprStructEq_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_ExprStructEq_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0_value: crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 66, 105, 110, 100, 101, 114, 78, 97, 109, 101, 72, 105, 110, 116, 46, 48, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 114, 101, 115, 111, 108, 118, 101, 66, 105, 110, 100, 101, 114, 78, 97, 109, 101, 72, 105, 110, 116, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1_value: crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 120, 115, 46, 115, 105, 122, 101, 32, 62, 32, 98, 105, 100, 120, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_resolveBinderNameHint___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_resolveBinderNameHint___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_resolveBinderNameHint___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_resolveBinderNameHint___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_resolveBinderNameHint___closed__2_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Expr_resolveBinderNameHint___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_resolveBinderNameHint___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Expr_hasBinderNameHint___lam__0(
    mut v_e_728_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: u8 = 0;
    v___x_729_ = l_Lean_Expr_hasBinderNameHint___lam__0___closed__1;
    v___x_730_ = l_Lean_Expr_isConstOf(v_e_728_, v___x_729_);
    return v___x_730_;
}
pub unsafe fn l_Lean_Expr_hasBinderNameHint___lam__0___boxed(
    mut v_e_731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_732_: u8 = 0;
    let mut v_r_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_732_ = l_Lean_Expr_hasBinderNameHint___lam__0(v_e_731_);
    crate::leanh::lean_dec_ref(v_e_731_);
    v_r_733_ = crate::leanh::lean_box((v_res_732_) as usize);
    return v_r_733_;
}
pub unsafe fn l_Lean_Expr_hasBinderNameHint(mut v_e_735_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___f_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_736_ = l_Lean_Expr_hasBinderNameHint___closed__0;
    v___x_737_ = lean_find_expr(v___f_736_, v_e_735_);
    if crate::leanh::lean_obj_tag(v___x_737_) == 0 {
        let mut v___x_738_: u8 = 0;
        v___x_738_ = 0;
        return v___x_738_;
    } else {
        let mut v___x_739_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_737_, 1);
        v___x_739_ = 1;
        return v___x_739_;
    }
}
pub unsafe fn l_Lean_Expr_hasBinderNameHint___boxed(
    mut v_e_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_741_: u8 = 0;
    let mut v_r_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_741_ = l_Lean_Expr_hasBinderNameHint(v_e_740_);
    crate::leanh::lean_dec_ref(v_e_740_);
    v_r_742_ = crate::leanh::lean_box((v_res_741_) as usize);
    return v_r_742_;
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_enterScope(
    mut v_name_743_: *mut crate::leanh::LeanObject,
    mut v_xs_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_745_ = lean_array_push(v_xs_744_, v_name_743_);
    return v___x_745_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_746_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_746_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(
    mut v_msg_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_748_ = crate::leanh::lean_box(0);
    v___x_749_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0);
    v___x_750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_750_, 0, v___x_748_);
    crate::leanh::lean_ctor_set(v___x_750_, 1, v___x_749_);
    v___x_751_ = lean_panic_fn_borrowed(v___x_750_, v_msg_747_);
    crate::leanh::lean_dec_ref_known(v___x_750_, 2);
    return v___x_751_;
}
pub unsafe fn _init_l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__2;
    v___x_756_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_757_ = crate::leanh::lean_unsigned_to_nat(26);
    v___x_758_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__1;
    v___x_759_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0;
    v___x_760_ =
        l_mkPanicMessageWithDecl(v___x_759_, v___x_758_, v___x_757_, v___x_756_, v___x_755_);
    return v___x_760_;
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(
    mut v_xs_761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: u8 = 0;
    v___x_762_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_763_ = lean_array_get_size(v_xs_761_);
    v___x_764_ = lean_nat_dec_lt(v___x_762_, v___x_763_);
    if v___x_764_ == 0 {
        let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_761_);
        v___x_765_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3_once
            ),
            _init_l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__3,
        );
        v___x_766_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(
            v___x_765_,
        );
        return v___x_766_;
    } else {
        let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_767_ = crate::leanh::lean_box(0);
        v___x_768_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_769_ = lean_nat_sub(v___x_763_, v___x_768_);
        v___x_770_ = lean_array_get(v___x_767_, v_xs_761_, v___x_769_);
        crate::leanh::lean_dec(v___x_769_);
        v___x_771_ = lean_array_pop(v_xs_761_);
        v___x_772_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_772_, 0, v___x_770_);
        crate::leanh::lean_ctor_set(v___x_772_, 1, v___x_771_);
        return v___x_772_;
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(
    mut v_msg_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0___closed__0);
    v___x_775_ = lean_panic_fn_borrowed(v___x_774_, v_msg_773_);
    return v___x_775_;
}
pub unsafe fn _init_l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_778_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1;
    v___x_779_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_780_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_781_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__0;
    v___x_782_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0;
    v___x_783_ =
        l_mkPanicMessageWithDecl(v___x_782_, v___x_781_, v___x_780_, v___x_779_, v___x_778_);
    return v___x_783_;
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(
    mut v_bidx_784_: *mut crate::leanh::LeanObject,
    mut v_name_785_: *mut crate::leanh::LeanObject,
    mut v_xs_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: u8 = 0;
    v___x_787_ = lean_array_get_size(v_xs_786_);
    v___x_788_ = lean_nat_dec_lt(v_bidx_784_, v___x_787_);
    if v___x_788_ == 0 {
        let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_786_);
        crate::leanh::lean_dec(v_name_785_);
        v___x_789_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2_once
            ),
            _init_l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__2,
        );
        v___x_790_ =
            l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(
                v___x_789_,
            );
        return v___x_790_;
    } else {
        let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_791_ = lean_nat_sub(v___x_787_, v_bidx_784_);
        v___x_792_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_793_ = lean_nat_sub(v___x_791_, v___x_792_);
        crate::leanh::lean_dec(v___x_791_);
        v___x_794_ = lean_array_set(v_xs_786_, v___x_793_, v_name_785_);
        crate::leanh::lean_dec(v___x_793_);
        return v___x_794_;
    }
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___boxed(
    mut v_bidx_795_: *mut crate::leanh::LeanObject,
    mut v_name_796_: *mut crate::leanh::LeanObject,
    mut v_xs_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(
        v_bidx_795_,
        v_name_796_,
        v_xs_797_,
    );
    crate::leanh::lean_dec(v_bidx_795_);
    return v_res_798_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(
    mut v_msg_800_: *mut crate::leanh::LeanObject,
    mut v___y_801_: *mut crate::leanh::LeanObject,
    mut v___y_802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289__overap_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_804_ =
        l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___closed__0;
    v___x_289__overap_805_ = lean_panic_fn_borrowed(v___f_804_, v_msg_800_);
    crate::leanh::lean_inc(v___y_802_);
    crate::leanh::lean_inc_ref(v___y_801_);
    v___x_806_ = crate::leanh::lean_apply_3(
        v___x_289__overap_805_,
        v___y_801_,
        v___y_802_,
        crate::leanh::lean_box(0),
    );
    return v___x_806_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0___boxed(
    mut v_msg_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
    mut v___y_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_811_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(
        v_msg_807_, v___y_808_, v___y_809_,
    );
    crate::leanh::lean_dec(v___y_809_);
    crate::leanh::lean_dec_ref(v___y_808_);
    return v_res_811_;
}
pub unsafe fn _init_l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___closed__1;
    v___x_814_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_815_ = crate::leanh::lean_unsigned_to_nat(34);
    v___x_816_ = l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__0;
    v___x_817_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0;
    v___x_818_ =
        l_mkPanicMessageWithDecl(v___x_817_, v___x_816_, v___x_815_, v___x_814_, v___x_813_);
    return v___x_818_;
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(
    mut v_bidx_819_: *mut crate::leanh::LeanObject,
    mut v_xs_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: u8 = 0;
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_842_: u8 = 0;
    let mut v_a_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_846_: u8 = 0;
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_824_ = lean_array_get_size(v_xs_820_);
                v___x_825_ = lean_nat_dec_lt(v_bidx_819_, v___x_824_);
                if v___x_825_ == 0 {
                    crate::leanh::lean_dec_ref(v_xs_820_);
                    v___x_826_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1_once
                        ),
                        _init_l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___closed__1,
                    );
                    v___x_827_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(v___x_826_, v_a_821_, v_a_822_);
                    return v___x_827_;
                } else {
                    v___x_828_ = crate::leanh::lean_box(0);
                    v___x_829_ = lean_nat_sub(v___x_824_, v_bidx_819_);
                    v___x_830_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_831_ = lean_nat_sub(v___x_829_, v___x_830_);
                    crate::leanh::lean_dec(v___x_829_);
                    v_name_832_ = lean_array_get_borrowed(v___x_828_, v_xs_820_, v___x_831_);
                    crate::leanh::lean_inc(v_name_832_);
                    v___x_833_ = l_Lean_Core_mkFreshUserName(v_name_832_, v_a_821_, v_a_822_);
                    if crate::leanh::lean_obj_tag(v___x_833_) == 0 {
                        v_a_834_ = crate::leanh::lean_ctor_get(v___x_833_, 0);
                        v_isSharedCheck_842_ = (!crate::leanh::lean_is_exclusive(v___x_833_)) as u8;
                        if v_isSharedCheck_842_ == 0 {
                            v___x_836_ = v___x_833_;
                            v_isShared_837_ = v_isSharedCheck_842_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_834_);
                            crate::leanh::lean_dec(v___x_833_);
                            v___x_836_ = crate::leanh::lean_box(0);
                            v_isShared_837_ = v_isSharedCheck_842_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_831_);
                        crate::leanh::lean_dec_ref(v_xs_820_);
                        v_a_843_ = crate::leanh::lean_ctor_get(v___x_833_, 0);
                        v_isSharedCheck_850_ = (!crate::leanh::lean_is_exclusive(v___x_833_)) as u8;
                        if v_isSharedCheck_850_ == 0 {
                            v___x_845_ = v___x_833_;
                            v_isShared_846_ = v_isSharedCheck_850_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_843_);
                            crate::leanh::lean_dec(v___x_833_);
                            v___x_845_ = crate::leanh::lean_box(0);
                            v_isShared_846_ = v_isSharedCheck_850_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_838_ = lean_array_set(v_xs_820_, v___x_831_, v_a_834_);
                crate::leanh::lean_dec(v___x_831_);
                if v_isShared_837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_836_, 0, v___x_838_);
                    v___x_840_ = v___x_836_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_841_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
                    v___x_840_ = v_reuseFailAlloc_841_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_840_;
            }
            3 => {
                if v_isShared_846_ == 0 {
                    v___x_848_ = v___x_845_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_849_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
                    v___x_848_ = v_reuseFailAlloc_849_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___boxed(
    mut v_bidx_851_: *mut crate::leanh::LeanObject,
    mut v_xs_852_: *mut crate::leanh::LeanObject,
    mut v_a_853_: *mut crate::leanh::LeanObject,
    mut v_a_854_: *mut crate::leanh::LeanObject,
    mut v_a_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_856_ = l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(
        v_bidx_851_,
        v_xs_852_,
        v_a_853_,
        v_a_854_,
    );
    crate::leanh::lean_dec(v_a_854_);
    crate::leanh::lean_dec_ref(v_a_853_);
    crate::leanh::lean_dec(v_bidx_851_);
    return v_res_856_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_857_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(
    mut v_msg_862_: *mut crate::leanh::LeanObject,
    mut v___y_863_: *mut crate::leanh::LeanObject,
    mut v___y_864_: *mut crate::leanh::LeanObject,
    mut v___y_865_: *mut crate::leanh::LeanObject,
    mut v___y_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_873_: u8 = 0;
    let mut v_toFunctor_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_880_: u8 = 0;
    let mut v___f_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_13989__overap_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_913_: u8 = 0;
    let mut v_unused_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_915_: u8 = 0;
    let mut v_unused_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_868_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__0);
                v___x_869_ = l_StateRefT_x27_instMonad___redArg(v___x_868_);
                v_toApplicative_870_ = crate::leanh::lean_ctor_get(v___x_869_, 0);
                v_isSharedCheck_915_ = (!crate::leanh::lean_is_exclusive(v___x_869_)) as u8;
                if v_isSharedCheck_915_ == 0 {
                    v_unused_916_ = crate::leanh::lean_ctor_get(v___x_869_, 1);
                    crate::leanh::lean_dec(v_unused_916_);
                    v___x_872_ = v___x_869_;
                    v_isShared_873_ = v_isSharedCheck_915_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_870_);
                    crate::leanh::lean_dec(v___x_869_);
                    v___x_872_ = crate::leanh::lean_box(0);
                    v_isShared_873_ = v_isSharedCheck_915_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_874_ = crate::leanh::lean_ctor_get(v_toApplicative_870_, 0);
                v_toSeq_875_ = crate::leanh::lean_ctor_get(v_toApplicative_870_, 2);
                v_toSeqLeft_876_ = crate::leanh::lean_ctor_get(v_toApplicative_870_, 3);
                v_toSeqRight_877_ = crate::leanh::lean_ctor_get(v_toApplicative_870_, 4);
                v_isSharedCheck_913_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_870_)) as u8;
                if v_isSharedCheck_913_ == 0 {
                    v_unused_914_ = crate::leanh::lean_ctor_get(v_toApplicative_870_, 1);
                    crate::leanh::lean_dec(v_unused_914_);
                    v___x_879_ = v_toApplicative_870_;
                    v_isShared_880_ = v_isSharedCheck_913_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_877_);
                    crate::leanh::lean_inc(v_toSeqLeft_876_);
                    crate::leanh::lean_inc(v_toSeq_875_);
                    crate::leanh::lean_inc(v_toFunctor_874_);
                    crate::leanh::lean_dec(v_toApplicative_870_);
                    v___x_879_ = crate::leanh::lean_box(0);
                    v_isShared_880_ = v_isSharedCheck_913_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_881_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__1;
                v___f_882_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_874_);
                v___f_883_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_883_, 0, v_toFunctor_874_);
                v___f_884_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_884_, 0, v_toFunctor_874_);
                v___x_885_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_885_, 0, v___f_883_);
                crate::leanh::lean_ctor_set(v___x_885_, 1, v___f_884_);
                v___f_886_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_886_, 0, v_toSeqRight_877_);
                v___f_887_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_887_, 0, v_toSeqLeft_876_);
                v___f_888_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_888_, 0, v_toSeq_875_);
                if v_isShared_880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_879_, 4, v___f_886_);
                    crate::leanh::lean_ctor_set(v___x_879_, 3, v___f_887_);
                    crate::leanh::lean_ctor_set(v___x_879_, 2, v___f_888_);
                    crate::leanh::lean_ctor_set(v___x_879_, 1, v___f_881_);
                    crate::leanh::lean_ctor_set(v___x_879_, 0, v___x_885_);
                    v___x_890_ = v___x_879_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_912_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_912_, 1, v___f_881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_912_, 2, v___f_888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_912_, 3, v___f_887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_912_, 4, v___f_886_);
                    v___x_890_ = v_reuseFailAlloc_912_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_873_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_872_, 1, v___f_882_);
                    crate::leanh::lean_ctor_set(v___x_872_, 0, v___x_890_);
                    v___x_892_ = v___x_872_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_911_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_911_, 1, v___f_882_);
                    v___x_892_ = v_reuseFailAlloc_911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_893_ = crate::leanh::lean_box(0);
                v___x_894_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__3;
                v___x_895_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___closed__4;
                crate::leanh::lean_inc_ref_n(v___x_892_, 6);
                v___f_896_ = crate::leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_896_, 0, v___x_892_);
                v___f_897_ = crate::leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_897_, 0, v___x_892_);
                v___f_898_ = crate::leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_898_, 0, v___x_892_);
                v___f_899_ = crate::leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_899_, 0, v___x_892_);
                v___x_900_ =
                    crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___x_900_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_900_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_900_, 2, v___x_892_);
                v___x_901_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_901_, 0, v___x_900_);
                crate::leanh::lean_ctor_set(v___x_901_, 1, v___f_896_);
                v___x_902_ =
                    crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
                crate::leanh::lean_closure_set(v___x_902_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_902_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_902_, 2, v___x_892_);
                v___x_903_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_903_, 0, v___x_901_);
                crate::leanh::lean_ctor_set(v___x_903_, 1, v___x_902_);
                crate::leanh::lean_ctor_set(v___x_903_, 2, v___f_897_);
                crate::leanh::lean_ctor_set(v___x_903_, 3, v___f_898_);
                crate::leanh::lean_ctor_set(v___x_903_, 4, v___f_899_);
                v___x_904_ =
                    crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___x_904_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_904_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_904_, 2, v___x_892_);
                v___x_905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_905_, 0, v___x_903_);
                crate::leanh::lean_ctor_set(v___x_905_, 1, v___x_904_);
                v___x_906_ = l_Lean_MonadCacheT_instMonad___redArg(
                    v___x_893_, v___x_894_, v___x_895_, v___x_905_,
                );
                v___x_907_ = l_Lean_instInhabitedExpr;
                v___x_908_ = l_instInhabitedOfMonad___redArg(v___x_906_, v___x_907_);
                v___x_13989__overap_909_ = lean_panic_fn_borrowed(v___x_908_, v_msg_862_);
                crate::leanh::lean_dec(v___x_908_);
                crate::leanh::lean_inc(v___y_866_);
                crate::leanh::lean_inc_ref(v___y_865_);
                crate::leanh::lean_inc(v___y_863_);
                v___x_910_ = crate::leanh::lean_apply_5(
                    v___x_13989__overap_909_,
                    v___y_863_,
                    v___y_864_,
                    v___y_865_,
                    v___y_866_,
                    crate::leanh::lean_box(0),
                );
                return v___x_910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2___boxed(
    mut v_msg_917_: *mut crate::leanh::LeanObject,
    mut v___y_918_: *mut crate::leanh::LeanObject,
    mut v___y_919_: *mut crate::leanh::LeanObject,
    mut v___y_920_: *mut crate::leanh::LeanObject,
    mut v___y_921_: *mut crate::leanh::LeanObject,
    mut v___y_922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_923_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(v_msg_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
    crate::leanh::lean_dec(v___y_921_);
    crate::leanh::lean_dec_ref(v___y_920_);
    crate::leanh::lean_dec(v___y_918_);
    return v_res_923_;
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(
    mut v_fst_924_: *mut crate::leanh::LeanObject,
    mut v_____r_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
    mut v___y_929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_931_, 0, v_fst_924_);
    crate::leanh::lean_ctor_set(v___x_931_, 1, v___y_927_);
    v___x_932_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_932_, 0, v___x_931_);
    return v___x_932_;
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0___boxed(
    mut v_fst_933_: *mut crate::leanh::LeanObject,
    mut v_____r_934_: *mut crate::leanh::LeanObject,
    mut v___y_935_: *mut crate::leanh::LeanObject,
    mut v___y_936_: *mut crate::leanh::LeanObject,
    mut v___y_937_: *mut crate::leanh::LeanObject,
    mut v___y_938_: *mut crate::leanh::LeanObject,
    mut v___y_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_940_ =
        l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(
            v_fst_933_,
            v_____r_934_,
            v___y_935_,
            v___y_936_,
            v___y_937_,
            v___y_938_,
        );
    crate::leanh::lean_dec(v___y_938_);
    crate::leanh::lean_dec_ref(v___y_937_);
    crate::leanh::lean_dec(v___y_935_);
    return v_res_940_;
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(
    mut v___f_941_: *mut crate::leanh::LeanObject,
    mut v_bidx_942_: *mut crate::leanh::LeanObject,
    mut v_n_943_: *mut crate::leanh::LeanObject,
    mut v_binderType_944_: *mut crate::leanh::LeanObject,
    mut v_body_945_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_946_: u8,
    mut v___y_947_: *mut crate::leanh::LeanObject,
    mut v___y_948_: *mut crate::leanh::LeanObject,
    mut v___y_949_: *mut crate::leanh::LeanObject,
    mut v___y_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = crate::leanh::lean_box(0);
    v___x_953_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(
        v_bidx_942_,
        v_n_943_,
        v___y_948_,
    );
    crate::leanh::lean_inc(v___y_950_);
    crate::leanh::lean_inc_ref(v___y_949_);
    crate::leanh::lean_inc(v___y_947_);
    v___x_954_ = crate::leanh::lean_apply_6(
        v___f_941_,
        v___x_952_,
        v___y_947_,
        v___x_953_,
        v___y_949_,
        v___y_950_,
        crate::leanh::lean_box(0),
    );
    return v___x_954_;
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1___boxed(
    mut v___f_955_: *mut crate::leanh::LeanObject,
    mut v_bidx_956_: *mut crate::leanh::LeanObject,
    mut v_n_957_: *mut crate::leanh::LeanObject,
    mut v_binderType_958_: *mut crate::leanh::LeanObject,
    mut v_body_959_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
    mut v___y_962_: *mut crate::leanh::LeanObject,
    mut v___y_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderInfo_14512__boxed_966_: u8 = 0;
    let mut v_res_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_14512__boxed_966_ = (crate::leanh::lean_unbox(v_binderInfo_960_) as u8);
    v_res_967_ =
        l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(
            v___f_955_,
            v_bidx_956_,
            v_n_957_,
            v_binderType_958_,
            v_body_959_,
            v_binderInfo_14512__boxed_966_,
            v___y_961_,
            v___y_962_,
            v___y_963_,
            v___y_964_,
        );
    crate::leanh::lean_dec(v___y_964_);
    crate::leanh::lean_dec_ref(v___y_963_);
    crate::leanh::lean_dec(v___y_961_);
    crate::leanh::lean_dec_ref(v_body_959_);
    crate::leanh::lean_dec_ref(v_binderType_958_);
    crate::leanh::lean_dec(v_bidx_956_);
    return v_res_967_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_x_968_: *mut crate::leanh::LeanObject,
    mut v_x_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_975_: u8 = 0;
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: u64 = 0;
    let mut v___x_978_: u64 = 0;
    let mut v___x_979_: u64 = 0;
    let mut v_fold_980_: u64 = 0;
    let mut v___x_981_: u64 = 0;
    let mut v___x_982_: u64 = 0;
    let mut v___x_983_: u64 = 0;
    let mut v___x_984_: usize = 0;
    let mut v___x_985_: usize = 0;
    let mut v___x_986_: usize = 0;
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: usize = 0;
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_969_) == 0 {
                    return v_x_968_;
                } else {
                    v_key_970_ = crate::leanh::lean_ctor_get(v_x_969_, 0);
                    v_value_971_ = crate::leanh::lean_ctor_get(v_x_969_, 1);
                    v_tail_972_ = crate::leanh::lean_ctor_get(v_x_969_, 2);
                    v_isSharedCheck_995_ = (!crate::leanh::lean_is_exclusive(v_x_969_)) as u8;
                    if v_isSharedCheck_995_ == 0 {
                        v___x_974_ = v_x_969_;
                        v_isShared_975_ = v_isSharedCheck_995_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_972_);
                        crate::leanh::lean_inc(v_value_971_);
                        crate::leanh::lean_inc(v_key_970_);
                        crate::leanh::lean_dec(v_x_969_);
                        v___x_974_ = crate::leanh::lean_box(0);
                        v_isShared_975_ = v_isSharedCheck_995_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_976_ = lean_array_get_size(v_x_968_);
                v___x_977_ = l_Lean_ExprStructEq_hash(v_key_970_);
                v___x_978_ = 32u64;
                v___x_979_ = lean_uint64_shift_right(v___x_977_, v___x_978_);
                v_fold_980_ = lean_uint64_xor(v___x_977_, v___x_979_);
                v___x_981_ = 16u64;
                v___x_982_ = lean_uint64_shift_right(v_fold_980_, v___x_981_);
                v___x_983_ = lean_uint64_xor(v_fold_980_, v___x_982_);
                v___x_984_ = lean_uint64_to_usize(v___x_983_);
                v___x_985_ = lean_usize_of_nat(v___x_976_);
                v___x_986_ = 1usize;
                v___x_987_ = lean_usize_sub(v___x_985_, v___x_986_);
                v___x_988_ = lean_usize_land(v___x_984_, v___x_987_);
                v___x_989_ = lean_array_uget_borrowed(v_x_968_, v___x_988_);
                crate::leanh::lean_inc(v___x_989_);
                if v_isShared_975_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_974_, 2, v___x_989_);
                    v___x_991_ = v___x_974_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_994_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_994_, 0, v_key_970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_994_, 1, v_value_971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_994_, 2, v___x_989_);
                    v___x_991_ = v_reuseFailAlloc_994_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_992_ = lean_array_uset(v_x_968_, v___x_988_, v___x_991_);
                v_x_968_ = v___x_992_;
                v_x_969_ = v_tail_972_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(
    mut v_i_996_: *mut crate::leanh::LeanObject,
    mut v_source_997_: *mut crate::leanh::LeanObject,
    mut v_target_998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    let mut v_es_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_999_ = lean_array_get_size(v_source_997_);
                v___x_1000_ = lean_nat_dec_lt(v_i_996_, v___x_999_);
                if v___x_1000_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_997_);
                    crate::leanh::lean_dec(v_i_996_);
                    return v_target_998_;
                } else {
                    v_es_1001_ = lean_array_fget(v_source_997_, v_i_996_);
                    v___x_1002_ = crate::leanh::lean_box(0);
                    v_source_1003_ = lean_array_fset(v_source_997_, v_i_996_, v___x_1002_);
                    v_target_1004_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(v_target_998_, v_es_1001_);
                    v___x_1005_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1006_ = lean_nat_add(v_i_996_, v___x_1005_);
                    crate::leanh::lean_dec(v_i_996_);
                    v_i_996_ = v___x_1006_;
                    v_source_997_ = v_source_1003_;
                    v_target_998_ = v_target_1004_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(
    mut v_data_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = lean_array_get_size(v_data_1008_);
    v___x_1010_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1011_ = lean_nat_mul(v___x_1009_, v___x_1010_);
    v___x_1012_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1013_ = crate::leanh::lean_box(0);
    v___x_1014_ = lean_mk_array(v_nbuckets_1011_, v___x_1013_);
    v___x_1015_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(v___x_1012_, v_data_1008_, v___x_1014_);
    return v___x_1015_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(
    mut v_a_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1018_: u8 = 0;
    let mut v_key_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1017_) == 0 {
                    v___x_1018_ = 0;
                    return v___x_1018_;
                } else {
                    v_key_1019_ = crate::leanh::lean_ctor_get(v_x_1017_, 0);
                    v_tail_1020_ = crate::leanh::lean_ctor_get(v_x_1017_, 2);
                    v___x_1021_ = l_Lean_ExprStructEq_beq(v_key_1019_, v_a_1016_);
                    if v___x_1021_ == 0 {
                        v_x_1017_ = v_tail_1020_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1021_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg___boxed(
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_x_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1025_: u8 = 0;
    let mut v_r_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1025_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_1023_, v_x_1024_);
    crate::leanh::lean_dec(v_x_1024_);
    crate::leanh::lean_dec_ref(v_a_1023_);
    v_r_1026_ = crate::leanh::lean_box((v_res_1025_) as usize);
    return v_r_1026_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(
    mut v_a_1027_: *mut crate::leanh::LeanObject,
    mut v_b_1028_: *mut crate::leanh::LeanObject,
    mut v_x_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1035_: u8 = 0;
    let mut v___x_1036_: u8 = 0;
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1029_) == 0 {
                    crate::leanh::lean_dec(v_b_1028_);
                    crate::leanh::lean_dec_ref(v_a_1027_);
                    return v_x_1029_;
                } else {
                    v_key_1030_ = crate::leanh::lean_ctor_get(v_x_1029_, 0);
                    v_value_1031_ = crate::leanh::lean_ctor_get(v_x_1029_, 1);
                    v_tail_1032_ = crate::leanh::lean_ctor_get(v_x_1029_, 2);
                    v_isSharedCheck_1044_ = (!crate::leanh::lean_is_exclusive(v_x_1029_)) as u8;
                    if v_isSharedCheck_1044_ == 0 {
                        v___x_1034_ = v_x_1029_;
                        v_isShared_1035_ = v_isSharedCheck_1044_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1032_);
                        crate::leanh::lean_inc(v_value_1031_);
                        crate::leanh::lean_inc(v_key_1030_);
                        crate::leanh::lean_dec(v_x_1029_);
                        v___x_1034_ = crate::leanh::lean_box(0);
                        v_isShared_1035_ = v_isSharedCheck_1044_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1036_ = l_Lean_ExprStructEq_beq(v_key_1030_, v_a_1027_);
                if v___x_1036_ == 0 {
                    v___x_1037_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(v_a_1027_, v_b_1028_, v_tail_1032_);
                    if v_isShared_1035_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1034_, 2, v___x_1037_);
                        v___x_1039_ = v___x_1034_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1040_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_key_1030_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_value_1031_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1040_, 2, v___x_1037_);
                        v___x_1039_ = v_reuseFailAlloc_1040_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1031_);
                    crate::leanh::lean_dec(v_key_1030_);
                    if v_isShared_1035_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1034_, 1, v_b_1028_);
                        crate::leanh::lean_ctor_set(v___x_1034_, 0, v_a_1027_);
                        v___x_1042_ = v___x_1034_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1043_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1027_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_b_1028_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_tail_1032_);
                        v___x_1042_ = v_reuseFailAlloc_1043_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1039_;
            }
            3 => {
                return v___x_1042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(
    mut v_m_1045_: *mut crate::leanh::LeanObject,
    mut v_a_1046_: *mut crate::leanh::LeanObject,
    mut v_b_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: u64 = 0;
    let mut v___x_1055_: u64 = 0;
    let mut v___x_1056_: u64 = 0;
    let mut v_fold_1057_: u64 = 0;
    let mut v___x_1058_: u64 = 0;
    let mut v___x_1059_: u64 = 0;
    let mut v___x_1060_: u64 = 0;
    let mut v___x_1061_: usize = 0;
    let mut v___x_1062_: usize = 0;
    let mut v___x_1063_: usize = 0;
    let mut v___x_1064_: usize = 0;
    let mut v___x_1065_: usize = 0;
    let mut v_bkt_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: u8 = 0;
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    let mut v_val_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1048_ = crate::leanh::lean_ctor_get(v_m_1045_, 0);
                v_buckets_1049_ = crate::leanh::lean_ctor_get(v_m_1045_, 1);
                v_isSharedCheck_1092_ = (!crate::leanh::lean_is_exclusive(v_m_1045_)) as u8;
                if v_isSharedCheck_1092_ == 0 {
                    v___x_1051_ = v_m_1045_;
                    v_isShared_1052_ = v_isSharedCheck_1092_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1049_);
                    crate::leanh::lean_inc(v_size_1048_);
                    crate::leanh::lean_dec(v_m_1045_);
                    v___x_1051_ = crate::leanh::lean_box(0);
                    v_isShared_1052_ = v_isSharedCheck_1092_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1053_ = lean_array_get_size(v_buckets_1049_);
                v___x_1054_ = l_Lean_ExprStructEq_hash(v_a_1046_);
                v___x_1055_ = 32u64;
                v___x_1056_ = lean_uint64_shift_right(v___x_1054_, v___x_1055_);
                v_fold_1057_ = lean_uint64_xor(v___x_1054_, v___x_1056_);
                v___x_1058_ = 16u64;
                v___x_1059_ = lean_uint64_shift_right(v_fold_1057_, v___x_1058_);
                v___x_1060_ = lean_uint64_xor(v_fold_1057_, v___x_1059_);
                v___x_1061_ = lean_uint64_to_usize(v___x_1060_);
                v___x_1062_ = lean_usize_of_nat(v___x_1053_);
                v___x_1063_ = 1usize;
                v___x_1064_ = lean_usize_sub(v___x_1062_, v___x_1063_);
                v___x_1065_ = lean_usize_land(v___x_1061_, v___x_1064_);
                v_bkt_1066_ = lean_array_uget_borrowed(v_buckets_1049_, v___x_1065_);
                v___x_1067_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_1046_, v_bkt_1066_);
                if v___x_1067_ == 0 {
                    v___x_1068_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1069_ = lean_nat_add(v_size_1048_, v___x_1068_);
                    crate::leanh::lean_dec(v_size_1048_);
                    crate::leanh::lean_inc(v_bkt_1066_);
                    v___x_1070_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1070_, 0, v_a_1046_);
                    crate::leanh::lean_ctor_set(v___x_1070_, 1, v_b_1047_);
                    crate::leanh::lean_ctor_set(v___x_1070_, 2, v_bkt_1066_);
                    v_buckets_x27_1071_ =
                        lean_array_uset(v_buckets_1049_, v___x_1065_, v___x_1070_);
                    v___x_1072_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1073_ = lean_nat_mul(v_size_x27_1069_, v___x_1072_);
                    v___x_1074_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1075_ = lean_nat_div(v___x_1073_, v___x_1074_);
                    crate::leanh::lean_dec(v___x_1073_);
                    v___x_1076_ = lean_array_get_size(v_buckets_x27_1071_);
                    v___x_1077_ = lean_nat_dec_le(v___x_1075_, v___x_1076_);
                    crate::leanh::lean_dec(v___x_1075_);
                    if v___x_1077_ == 0 {
                        v_val_1078_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(v_buckets_x27_1071_);
                        if v_isShared_1052_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1051_, 1, v_val_1078_);
                            crate::leanh::lean_ctor_set(v___x_1051_, 0, v_size_x27_1069_);
                            v___x_1080_ = v___x_1051_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1081_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1081_,
                                0,
                                v_size_x27_1069_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_val_1078_);
                            v___x_1080_ = v_reuseFailAlloc_1081_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1052_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1051_, 1, v_buckets_x27_1071_);
                            crate::leanh::lean_ctor_set(v___x_1051_, 0, v_size_x27_1069_);
                            v___x_1083_ = v___x_1051_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1084_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1084_,
                                0,
                                v_size_x27_1069_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1084_,
                                1,
                                v_buckets_x27_1071_,
                            );
                            v___x_1083_ = v_reuseFailAlloc_1084_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1066_);
                    v___x_1085_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1086_ =
                        lean_array_uset(v_buckets_1049_, v___x_1065_, v___x_1085_);
                    v___x_1087_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(v_a_1046_, v_b_1047_, v_bkt_1066_);
                    v___x_1088_ = lean_array_uset(v_buckets_x27_1086_, v___x_1065_, v___x_1087_);
                    if v_isShared_1052_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1051_, 1, v___x_1088_);
                        v___x_1090_ = v___x_1051_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1091_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_size_1048_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1088_);
                        v___x_1090_ = v_reuseFailAlloc_1091_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1080_;
            }
            3 => {
                return v___x_1083_;
            }
            4 => {
                return v___x_1090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_x_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: u8 = 0;
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1094_) == 0 {
                    v___x_1095_ = crate::leanh::lean_box(0);
                    return v___x_1095_;
                } else {
                    v_key_1096_ = crate::leanh::lean_ctor_get(v_x_1094_, 0);
                    v_value_1097_ = crate::leanh::lean_ctor_get(v_x_1094_, 1);
                    v_tail_1098_ = crate::leanh::lean_ctor_get(v_x_1094_, 2);
                    v___x_1099_ = l_Lean_ExprStructEq_beq(v_key_1096_, v_a_1093_);
                    if v___x_1099_ == 0 {
                        v_x_1094_ = v_tail_1098_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1097_);
                        v___x_1101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1101_, 0, v_value_1097_);
                        return v___x_1101_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg___boxed(
    mut v_a_1102_: *mut crate::leanh::LeanObject,
    mut v_x_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1104_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(v_a_1102_, v_x_1103_);
    crate::leanh::lean_dec(v_x_1103_);
    crate::leanh::lean_dec_ref(v_a_1102_);
    return v_res_1104_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(
    mut v_m_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u64 = 0;
    let mut v___x_1110_: u64 = 0;
    let mut v___x_1111_: u64 = 0;
    let mut v_fold_1112_: u64 = 0;
    let mut v___x_1113_: u64 = 0;
    let mut v___x_1114_: u64 = 0;
    let mut v___x_1115_: u64 = 0;
    let mut v___x_1116_: usize = 0;
    let mut v___x_1117_: usize = 0;
    let mut v___x_1118_: usize = 0;
    let mut v___x_1119_: usize = 0;
    let mut v___x_1120_: usize = 0;
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1107_ = crate::leanh::lean_ctor_get(v_m_1105_, 1);
    v___x_1108_ = lean_array_get_size(v_buckets_1107_);
    v___x_1109_ = l_Lean_ExprStructEq_hash(v_a_1106_);
    v___x_1110_ = 32u64;
    v___x_1111_ = lean_uint64_shift_right(v___x_1109_, v___x_1110_);
    v_fold_1112_ = lean_uint64_xor(v___x_1109_, v___x_1111_);
    v___x_1113_ = 16u64;
    v___x_1114_ = lean_uint64_shift_right(v_fold_1112_, v___x_1113_);
    v___x_1115_ = lean_uint64_xor(v_fold_1112_, v___x_1114_);
    v___x_1116_ = lean_uint64_to_usize(v___x_1115_);
    v___x_1117_ = lean_usize_of_nat(v___x_1108_);
    v___x_1118_ = 1usize;
    v___x_1119_ = lean_usize_sub(v___x_1117_, v___x_1118_);
    v___x_1120_ = lean_usize_land(v___x_1116_, v___x_1119_);
    v___x_1121_ = lean_array_uget_borrowed(v_buckets_1107_, v___x_1120_);
    v___x_1122_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(v_a_1106_, v___x_1121_);
    return v___x_1122_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg___boxed(
    mut v_m_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v_m_1123_, v_a_1124_);
    crate::leanh::lean_dec_ref(v_a_1124_);
    crate::leanh::lean_dec_ref(v_m_1123_);
    return v_res_1125_;
}
pub unsafe fn _init_l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ =
        l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__1;
    v___x_1129_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1130_ = crate::leanh::lean_unsigned_to_nat(72);
    v___x_1131_ =
        l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__0;
    v___x_1132_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope___closed__0;
    v___x_1133_ = l_mkPanicMessageWithDecl(
        v___x_1132_,
        v___x_1131_,
        v___x_1130_,
        v___x_1129_,
        v___x_1128_,
    );
    return v___x_1133_;
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(
    mut v_e_1134_: *mut crate::leanh::LeanObject,
    mut v_a_1135_: *mut crate::leanh::LeanObject,
    mut v_a_1136_: *mut crate::leanh::LeanObject,
    mut v_a_1137_: *mut crate::leanh::LeanObject,
    mut v_a_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: u8 = 0;
    let mut v_binderName_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1159_: u8 = 0;
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut v_binderName_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1183_: u8 = 0;
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1203_: u8 = 0;
    let mut v_declName_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1208_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut v_fn_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1245_: u8 = 0;
    let mut v___y_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1252_: u8 = 0;
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: usize = 0;
    let mut v___x_1255_: usize = 0;
    let mut v___x_1256_: u8 = 0;
    let mut v___x_1257_: usize = 0;
    let mut v___x_1258_: usize = 0;
    let mut v___x_1259_: u8 = 0;
    let mut v_isSharedCheck_1260_: u8 = 0;
    let mut v_data_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___y_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: usize = 0;
    let mut v___x_1276_: usize = 0;
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut v_typeName_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v___y_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: usize = 0;
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1299_: u8 = 0;
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1316_: u8 = 0;
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1321_: u8 = 0;
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: u8 = 0;
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1151_ = lean_st_ref_get(v_a_1135_);
                v___x_1152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v___x_1151_, v_e_1134_);
                crate::leanh::lean_dec(v___x_1151_);
                if crate::leanh::lean_obj_tag(v___x_1152_) == 0 {
                    v___x_1153_ = l_Lean_Expr_hasBinderNameHint___lam__0___closed__1;
                    v___x_1154_ = crate::leanh::lean_unsigned_to_nat(6);
                    v___x_1155_ = l_Lean_Expr_isAppOfArity(v_e_1134_, v___x_1153_, v___x_1154_);
                    if v___x_1155_ == 0 {
                        match crate::leanh::lean_obj_tag(v_e_1134_) {
                            7 => {
                                v_binderName_1156_ = crate::leanh::lean_ctor_get(v_e_1134_, 0);
                                v_binderType_1157_ = crate::leanh::lean_ctor_get(v_e_1134_, 1);
                                v_body_1158_ = crate::leanh::lean_ctor_get(v_e_1134_, 2);
                                v_binderInfo_1159_ = crate::leanh::lean_ctor_get_uint8(
                                    v_e_1134_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                        as u32,
                                );
                                crate::leanh::lean_inc_ref(v_binderType_1157_);
                                v___x_1160_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_binderType_1157_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
                                if crate::leanh::lean_obj_tag(v___x_1160_) == 0 {
                                    v_a_1161_ = crate::leanh::lean_ctor_get(v___x_1160_, 0);
                                    crate::leanh::lean_inc(v_a_1161_);
                                    crate::leanh::lean_dec_ref_known(v___x_1160_, 1);
                                    v_fst_1162_ = crate::leanh::lean_ctor_get(v_a_1161_, 0);
                                    crate::leanh::lean_inc(v_fst_1162_);
                                    v_snd_1163_ = crate::leanh::lean_ctor_get(v_a_1161_, 1);
                                    crate::leanh::lean_inc(v_snd_1163_);
                                    crate::leanh::lean_dec(v_a_1161_);
                                    crate::leanh::lean_inc(v_binderName_1156_);
                                    v___x_1164_ = lean_array_push(v_snd_1163_, v_binderName_1156_);
                                    crate::leanh::lean_inc_ref(v_body_1158_);
                                    v___x_1165_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_1158_, v_a_1135_, v___x_1164_, v_a_1137_, v_a_1138_);
                                    if crate::leanh::lean_obj_tag(v___x_1165_) == 0 {
                                        v_a_1166_ = crate::leanh::lean_ctor_get(v___x_1165_, 0);
                                        crate::leanh::lean_inc(v_a_1166_);
                                        crate::leanh::lean_dec_ref_known(v___x_1165_, 1);
                                        v_fst_1167_ = crate::leanh::lean_ctor_get(v_a_1166_, 0);
                                        crate::leanh::lean_inc(v_fst_1167_);
                                        v_snd_1168_ = crate::leanh::lean_ctor_get(v_a_1166_, 1);
                                        crate::leanh::lean_inc(v_snd_1168_);
                                        crate::leanh::lean_dec(v_a_1166_);
                                        v___x_1169_ =
                                            l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(
                                                v_snd_1168_,
                                            );
                                        v_fst_1170_ = crate::leanh::lean_ctor_get(v___x_1169_, 0);
                                        v_snd_1171_ = crate::leanh::lean_ctor_get(v___x_1169_, 1);
                                        v_isSharedCheck_1179_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1169_)) as u8;
                                        if v_isSharedCheck_1179_ == 0 {
                                            v___x_1173_ = v___x_1169_;
                                            v_isShared_1174_ = v_isSharedCheck_1179_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_snd_1171_);
                                            crate::leanh::lean_inc(v_fst_1170_);
                                            crate::leanh::lean_dec(v___x_1169_);
                                            v___x_1173_ = crate::leanh::lean_box(0);
                                            v_isShared_1174_ = v_isSharedCheck_1179_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_fst_1162_);
                                        v___y_1148_ = v___x_1165_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_1148_ = v___x_1160_;
                                    state = 2;
                                    continue;
                                }
                            }
                            6 => {
                                v_binderName_1180_ = crate::leanh::lean_ctor_get(v_e_1134_, 0);
                                v_binderType_1181_ = crate::leanh::lean_ctor_get(v_e_1134_, 1);
                                v_body_1182_ = crate::leanh::lean_ctor_get(v_e_1134_, 2);
                                v_binderInfo_1183_ = crate::leanh::lean_ctor_get_uint8(
                                    v_e_1134_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                        as u32,
                                );
                                crate::leanh::lean_inc_ref(v_binderType_1181_);
                                v___x_1184_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_binderType_1181_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
                                if crate::leanh::lean_obj_tag(v___x_1184_) == 0 {
                                    v_a_1185_ = crate::leanh::lean_ctor_get(v___x_1184_, 0);
                                    crate::leanh::lean_inc(v_a_1185_);
                                    crate::leanh::lean_dec_ref_known(v___x_1184_, 1);
                                    v_fst_1186_ = crate::leanh::lean_ctor_get(v_a_1185_, 0);
                                    crate::leanh::lean_inc(v_fst_1186_);
                                    v_snd_1187_ = crate::leanh::lean_ctor_get(v_a_1185_, 1);
                                    crate::leanh::lean_inc(v_snd_1187_);
                                    crate::leanh::lean_dec(v_a_1185_);
                                    crate::leanh::lean_inc(v_binderName_1180_);
                                    v___x_1188_ = lean_array_push(v_snd_1187_, v_binderName_1180_);
                                    crate::leanh::lean_inc_ref(v_body_1182_);
                                    v___x_1189_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_1182_, v_a_1135_, v___x_1188_, v_a_1137_, v_a_1138_);
                                    if crate::leanh::lean_obj_tag(v___x_1189_) == 0 {
                                        v_a_1190_ = crate::leanh::lean_ctor_get(v___x_1189_, 0);
                                        crate::leanh::lean_inc(v_a_1190_);
                                        crate::leanh::lean_dec_ref_known(v___x_1189_, 1);
                                        v_fst_1191_ = crate::leanh::lean_ctor_get(v_a_1190_, 0);
                                        crate::leanh::lean_inc(v_fst_1191_);
                                        v_snd_1192_ = crate::leanh::lean_ctor_get(v_a_1190_, 1);
                                        crate::leanh::lean_inc(v_snd_1192_);
                                        crate::leanh::lean_dec(v_a_1190_);
                                        v___x_1193_ =
                                            l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(
                                                v_snd_1192_,
                                            );
                                        v_fst_1194_ = crate::leanh::lean_ctor_get(v___x_1193_, 0);
                                        v_snd_1195_ = crate::leanh::lean_ctor_get(v___x_1193_, 1);
                                        v_isSharedCheck_1203_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1193_)) as u8;
                                        if v_isSharedCheck_1203_ == 0 {
                                            v___x_1197_ = v___x_1193_;
                                            v_isShared_1198_ = v_isSharedCheck_1203_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_snd_1195_);
                                            crate::leanh::lean_inc(v_fst_1194_);
                                            crate::leanh::lean_dec(v___x_1193_);
                                            v___x_1197_ = crate::leanh::lean_box(0);
                                            v_isShared_1198_ = v_isSharedCheck_1203_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_fst_1186_);
                                        v___y_1148_ = v___x_1189_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_1148_ = v___x_1184_;
                                    state = 2;
                                    continue;
                                }
                            }
                            8 => {
                                v_declName_1204_ = crate::leanh::lean_ctor_get(v_e_1134_, 0);
                                v_type_1205_ = crate::leanh::lean_ctor_get(v_e_1134_, 1);
                                v_value_1206_ = crate::leanh::lean_ctor_get(v_e_1134_, 2);
                                v_body_1207_ = crate::leanh::lean_ctor_get(v_e_1134_, 3);
                                v_nondep_1208_ = crate::leanh::lean_ctor_get_uint8(
                                    v_e_1134_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8)
                                        as u32,
                                );
                                crate::leanh::lean_inc_ref(v_type_1205_);
                                v___x_1209_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_type_1205_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
                                if crate::leanh::lean_obj_tag(v___x_1209_) == 0 {
                                    v_a_1210_ = crate::leanh::lean_ctor_get(v___x_1209_, 0);
                                    crate::leanh::lean_inc(v_a_1210_);
                                    crate::leanh::lean_dec_ref_known(v___x_1209_, 1);
                                    v_fst_1211_ = crate::leanh::lean_ctor_get(v_a_1210_, 0);
                                    crate::leanh::lean_inc(v_fst_1211_);
                                    v_snd_1212_ = crate::leanh::lean_ctor_get(v_a_1210_, 1);
                                    crate::leanh::lean_inc(v_snd_1212_);
                                    crate::leanh::lean_dec(v_a_1210_);
                                    crate::leanh::lean_inc_ref(v_value_1206_);
                                    v___x_1213_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_value_1206_, v_a_1135_, v_snd_1212_, v_a_1137_, v_a_1138_);
                                    if crate::leanh::lean_obj_tag(v___x_1213_) == 0 {
                                        v_a_1214_ = crate::leanh::lean_ctor_get(v___x_1213_, 0);
                                        crate::leanh::lean_inc(v_a_1214_);
                                        crate::leanh::lean_dec_ref_known(v___x_1213_, 1);
                                        v_fst_1215_ = crate::leanh::lean_ctor_get(v_a_1214_, 0);
                                        crate::leanh::lean_inc(v_fst_1215_);
                                        v_snd_1216_ = crate::leanh::lean_ctor_get(v_a_1214_, 1);
                                        crate::leanh::lean_inc(v_snd_1216_);
                                        crate::leanh::lean_dec(v_a_1214_);
                                        crate::leanh::lean_inc(v_declName_1204_);
                                        v___x_1217_ =
                                            lean_array_push(v_snd_1216_, v_declName_1204_);
                                        crate::leanh::lean_inc_ref(v_body_1207_);
                                        v___x_1218_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_body_1207_, v_a_1135_, v___x_1217_, v_a_1137_, v_a_1138_);
                                        if crate::leanh::lean_obj_tag(v___x_1218_) == 0 {
                                            v_a_1219_ = crate::leanh::lean_ctor_get(v___x_1218_, 0);
                                            crate::leanh::lean_inc(v_a_1219_);
                                            crate::leanh::lean_dec_ref_known(v___x_1218_, 1);
                                            v_fst_1220_ = crate::leanh::lean_ctor_get(v_a_1219_, 0);
                                            crate::leanh::lean_inc(v_fst_1220_);
                                            v_snd_1221_ = crate::leanh::lean_ctor_get(v_a_1219_, 1);
                                            crate::leanh::lean_inc(v_snd_1221_);
                                            crate::leanh::lean_dec(v_a_1219_);
                                            v___x_1222_ = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(v_snd_1221_);
                                            v_fst_1223_ =
                                                crate::leanh::lean_ctor_get(v___x_1222_, 0);
                                            v_snd_1224_ =
                                                crate::leanh::lean_ctor_get(v___x_1222_, 1);
                                            v_isSharedCheck_1232_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1222_))
                                                    as u8;
                                            if v_isSharedCheck_1232_ == 0 {
                                                v___x_1226_ = v___x_1222_;
                                                v_isShared_1227_ = v_isSharedCheck_1232_;
                                                state = 7;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_snd_1224_);
                                                crate::leanh::lean_inc(v_fst_1223_);
                                                crate::leanh::lean_dec(v___x_1222_);
                                                v___x_1226_ = crate::leanh::lean_box(0);
                                                v_isShared_1227_ = v_isSharedCheck_1232_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_fst_1215_);
                                            crate::leanh::lean_dec(v_fst_1211_);
                                            v___y_1148_ = v___x_1218_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_fst_1211_);
                                        v___y_1148_ = v___x_1213_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_1148_ = v___x_1209_;
                                    state = 2;
                                    continue;
                                }
                            }
                            5 => {
                                v_fn_1233_ = crate::leanh::lean_ctor_get(v_e_1134_, 0);
                                v_arg_1234_ = crate::leanh::lean_ctor_get(v_e_1134_, 1);
                                crate::leanh::lean_inc_ref(v_fn_1233_);
                                v___x_1235_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_fn_1233_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
                                if crate::leanh::lean_obj_tag(v___x_1235_) == 0 {
                                    v_a_1236_ = crate::leanh::lean_ctor_get(v___x_1235_, 0);
                                    crate::leanh::lean_inc(v_a_1236_);
                                    crate::leanh::lean_dec_ref_known(v___x_1235_, 1);
                                    v_fst_1237_ = crate::leanh::lean_ctor_get(v_a_1236_, 0);
                                    crate::leanh::lean_inc(v_fst_1237_);
                                    v_snd_1238_ = crate::leanh::lean_ctor_get(v_a_1236_, 1);
                                    crate::leanh::lean_inc(v_snd_1238_);
                                    crate::leanh::lean_dec(v_a_1236_);
                                    crate::leanh::lean_inc_ref(v_arg_1234_);
                                    v___x_1239_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_arg_1234_, v_a_1135_, v_snd_1238_, v_a_1137_, v_a_1138_);
                                    if crate::leanh::lean_obj_tag(v___x_1239_) == 0 {
                                        v_a_1240_ = crate::leanh::lean_ctor_get(v___x_1239_, 0);
                                        crate::leanh::lean_inc(v_a_1240_);
                                        crate::leanh::lean_dec_ref_known(v___x_1239_, 1);
                                        v_fst_1241_ = crate::leanh::lean_ctor_get(v_a_1240_, 0);
                                        v_snd_1242_ = crate::leanh::lean_ctor_get(v_a_1240_, 1);
                                        v_isSharedCheck_1260_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_1240_)) as u8;
                                        if v_isSharedCheck_1260_ == 0 {
                                            v___x_1244_ = v_a_1240_;
                                            v_isShared_1245_ = v_isSharedCheck_1260_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_snd_1242_);
                                            crate::leanh::lean_inc(v_fst_1241_);
                                            crate::leanh::lean_dec(v_a_1240_);
                                            v___x_1244_ = crate::leanh::lean_box(0);
                                            v_isShared_1245_ = v_isSharedCheck_1260_;
                                            state = 9;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_fst_1237_);
                                        v___y_1148_ = v___x_1239_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_1148_ = v___x_1235_;
                                    state = 2;
                                    continue;
                                }
                            }
                            10 => {
                                v_data_1261_ = crate::leanh::lean_ctor_get(v_e_1134_, 0);
                                v_expr_1262_ = crate::leanh::lean_ctor_get(v_e_1134_, 1);
                                crate::leanh::lean_inc_ref(v_expr_1262_);
                                v___x_1263_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_expr_1262_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
                                if crate::leanh::lean_obj_tag(v___x_1263_) == 0 {
                                    v_a_1264_ = crate::leanh::lean_ctor_get(v___x_1263_, 0);
                                    crate::leanh::lean_inc(v_a_1264_);
                                    crate::leanh::lean_dec_ref_known(v___x_1263_, 1);
                                    v_fst_1265_ = crate::leanh::lean_ctor_get(v_a_1264_, 0);
                                    v_snd_1266_ = crate::leanh::lean_ctor_get(v_a_1264_, 1);
                                    v_isSharedCheck_1279_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_1264_)) as u8;
                                    if v_isSharedCheck_1279_ == 0 {
                                        v___x_1268_ = v_a_1264_;
                                        v_isShared_1269_ = v_isSharedCheck_1279_;
                                        state = 13;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_snd_1266_);
                                        crate::leanh::lean_inc(v_fst_1265_);
                                        crate::leanh::lean_dec(v_a_1264_);
                                        v___x_1268_ = crate::leanh::lean_box(0);
                                        v_isShared_1269_ = v_isSharedCheck_1279_;
                                        state = 13;
                                        continue;
                                    }
                                } else {
                                    v___y_1148_ = v___x_1263_;
                                    state = 2;
                                    continue;
                                }
                            }
                            11 => {
                                v_typeName_1280_ = crate::leanh::lean_ctor_get(v_e_1134_, 0);
                                v_idx_1281_ = crate::leanh::lean_ctor_get(v_e_1134_, 1);
                                v_struct_1282_ = crate::leanh::lean_ctor_get(v_e_1134_, 2);
                                crate::leanh::lean_inc_ref(v_struct_1282_);
                                v___x_1283_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_struct_1282_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
                                if crate::leanh::lean_obj_tag(v___x_1283_) == 0 {
                                    v_a_1284_ = crate::leanh::lean_ctor_get(v___x_1283_, 0);
                                    crate::leanh::lean_inc(v_a_1284_);
                                    crate::leanh::lean_dec_ref_known(v___x_1283_, 1);
                                    v_fst_1285_ = crate::leanh::lean_ctor_get(v_a_1284_, 0);
                                    v_snd_1286_ = crate::leanh::lean_ctor_get(v_a_1284_, 1);
                                    v_isSharedCheck_1299_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_1284_)) as u8;
                                    if v_isSharedCheck_1299_ == 0 {
                                        v___x_1288_ = v_a_1284_;
                                        v_isShared_1289_ = v_isSharedCheck_1299_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_snd_1286_);
                                        crate::leanh::lean_inc(v_fst_1285_);
                                        crate::leanh::lean_dec(v_a_1284_);
                                        v___x_1288_ = crate::leanh::lean_box(0);
                                        v_isShared_1289_ = v_isSharedCheck_1299_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___y_1148_ = v___x_1283_;
                                    state = 2;
                                    continue;
                                }
                            }
                            _ => {
                                crate::leanh::lean_inc_ref_n(v_e_1134_, 2);
                                v___x_1300_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1300_, 0, v_e_1134_);
                                crate::leanh::lean_ctor_set(v___x_1300_, 1, v_a_1136_);
                                v_a_1141_ = v___x_1300_;
                                v_fst_1142_ = v_e_1134_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_e_1301_ = l_Lean_Expr_appArg_x21(v_e_1134_);
                        v___x_1302_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(v_e_1301_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
                        if crate::leanh::lean_obj_tag(v___x_1302_) == 0 {
                            v_a_1303_ = crate::leanh::lean_ctor_get(v___x_1302_, 0);
                            crate::leanh::lean_inc(v_a_1303_);
                            crate::leanh::lean_dec_ref_known(v___x_1302_, 1);
                            v_fst_1304_ = crate::leanh::lean_ctor_get(v_a_1303_, 0);
                            crate::leanh::lean_inc_n(v_fst_1304_, 2);
                            v_snd_1305_ = crate::leanh::lean_ctor_get(v_a_1303_, 1);
                            crate::leanh::lean_inc(v_snd_1305_);
                            crate::leanh::lean_dec(v_a_1303_);
                            v___f_1306_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                            crate::leanh::lean_closure_set(v___f_1306_, 0, v_fst_1304_);
                            v___x_1307_ = l_Lean_Expr_appFn_x21(v_e_1134_);
                            v___x_1308_ = l_Lean_Expr_appFn_x21(v___x_1307_);
                            v_v_1309_ = l_Lean_Expr_appArg_x21(v___x_1308_);
                            crate::leanh::lean_dec_ref(v___x_1308_);
                            if crate::leanh::lean_obj_tag(v_v_1309_) == 0 {
                                v_deBruijnIndex_1310_ = crate::leanh::lean_ctor_get(v_v_1309_, 0);
                                crate::leanh::lean_inc(v_deBruijnIndex_1310_);
                                crate::leanh::lean_dec_ref_known(v_v_1309_, 1);
                                v_b_1311_ = l_Lean_Expr_appArg_x21(v___x_1307_);
                                crate::leanh::lean_dec_ref(v___x_1307_);
                                v___x_1312_ = l_Lean_Expr_headBeta(v_b_1311_);
                                match crate::leanh::lean_obj_tag(v___x_1312_) {
                                    6 => {
                                        crate::leanh::lean_dec(v_fst_1304_);
                                        v_binderName_1313_ =
                                            crate::leanh::lean_ctor_get(v___x_1312_, 0);
                                        crate::leanh::lean_inc(v_binderName_1313_);
                                        v_binderType_1314_ =
                                            crate::leanh::lean_ctor_get(v___x_1312_, 1);
                                        crate::leanh::lean_inc_ref(v_binderType_1314_);
                                        v_body_1315_ = crate::leanh::lean_ctor_get(v___x_1312_, 2);
                                        crate::leanh::lean_inc_ref(v_body_1315_);
                                        v_binderInfo_1316_ = crate::leanh::lean_ctor_get_uint8(
                                            v___x_1312_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 3
                                                + 8)
                                                as u32,
                                        );
                                        crate::leanh::lean_dec_ref_known(v___x_1312_, 3);
                                        v___x_1317_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_1306_, v_deBruijnIndex_1310_, v_binderName_1313_, v_binderType_1314_, v_body_1315_, v_binderInfo_1316_, v_a_1135_, v_snd_1305_, v_a_1137_, v_a_1138_);
                                        crate::leanh::lean_dec_ref(v_body_1315_);
                                        crate::leanh::lean_dec_ref(v_binderType_1314_);
                                        crate::leanh::lean_dec(v_deBruijnIndex_1310_);
                                        v___y_1148_ = v___x_1317_;
                                        state = 2;
                                        continue;
                                    }
                                    7 => {
                                        crate::leanh::lean_dec(v_fst_1304_);
                                        v_binderName_1318_ =
                                            crate::leanh::lean_ctor_get(v___x_1312_, 0);
                                        crate::leanh::lean_inc(v_binderName_1318_);
                                        v_binderType_1319_ =
                                            crate::leanh::lean_ctor_get(v___x_1312_, 1);
                                        crate::leanh::lean_inc_ref(v_binderType_1319_);
                                        v_body_1320_ = crate::leanh::lean_ctor_get(v___x_1312_, 2);
                                        crate::leanh::lean_inc_ref(v_body_1320_);
                                        v_binderInfo_1321_ = crate::leanh::lean_ctor_get_uint8(
                                            v___x_1312_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 3
                                                + 8)
                                                as u32,
                                        );
                                        crate::leanh::lean_dec_ref_known(v___x_1312_, 3);
                                        v___x_1322_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__1(v___f_1306_, v_deBruijnIndex_1310_, v_binderName_1318_, v_binderType_1319_, v_body_1320_, v_binderInfo_1321_, v_a_1135_, v_snd_1305_, v_a_1137_, v_a_1138_);
                                        crate::leanh::lean_dec_ref(v_body_1320_);
                                        crate::leanh::lean_dec_ref(v_binderType_1319_);
                                        crate::leanh::lean_dec(v_deBruijnIndex_1310_);
                                        v___y_1148_ = v___x_1322_;
                                        state = 2;
                                        continue;
                                    }
                                    _ => {
                                        crate::leanh::lean_dec_ref(v___x_1312_);
                                        crate::leanh::lean_dec_ref(v___f_1306_);
                                        v___x_1323_ = lean_array_get_size(v_snd_1305_);
                                        v___x_1324_ =
                                            lean_nat_dec_lt(v_deBruijnIndex_1310_, v___x_1323_);
                                        if v___x_1324_ == 0 {
                                            crate::leanh::lean_dec(v_deBruijnIndex_1310_);
                                            crate::leanh::lean_dec(v_fst_1304_);
                                            v___x_1325_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2_once), _init_l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___closed__2);
                                            v___x_1326_ = l_panic___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__2(v___x_1325_, v_a_1135_, v_snd_1305_, v_a_1137_, v_a_1138_);
                                            v___y_1148_ = v___x_1326_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_1327_ = crate::leanh::lean_box(0);
                                            v___x_1328_ =
                                                lean_nat_sub(v___x_1323_, v_deBruijnIndex_1310_);
                                            v___x_1329_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_1330_ = lean_nat_sub(v___x_1328_, v___x_1329_);
                                            crate::leanh::lean_dec(v___x_1328_);
                                            v___x_1331_ = lean_array_get_borrowed(
                                                v___x_1327_,
                                                v_snd_1305_,
                                                v___x_1330_,
                                            );
                                            crate::leanh::lean_dec(v___x_1330_);
                                            crate::leanh::lean_inc(v___x_1331_);
                                            v___x_1332_ = l_Lean_Core_mkFreshUserName(
                                                v___x_1331_,
                                                v_a_1137_,
                                                v_a_1138_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_1332_) == 0 {
                                                v_a_1333_ =
                                                    crate::leanh::lean_ctor_get(v___x_1332_, 0);
                                                crate::leanh::lean_inc(v_a_1333_);
                                                crate::leanh::lean_dec_ref_known(v___x_1332_, 1);
                                                v___x_1334_ = crate::leanh::lean_box(0);
                                                v___x_1335_ = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(v_deBruijnIndex_1310_, v_a_1333_, v_snd_1305_);
                                                crate::leanh::lean_dec(v_deBruijnIndex_1310_);
                                                v___x_1336_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_1304_, v___x_1334_, v_a_1135_, v___x_1335_, v_a_1137_, v_a_1138_);
                                                v___y_1148_ = v___x_1336_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_deBruijnIndex_1310_);
                                                crate::leanh::lean_dec(v_snd_1305_);
                                                crate::leanh::lean_dec(v_fst_1304_);
                                                crate::leanh::lean_dec_ref(v_e_1134_);
                                                v_a_1337_ =
                                                    crate::leanh::lean_ctor_get(v___x_1332_, 0);
                                                v_isSharedCheck_1344_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_1332_))
                                                        as u8;
                                                if v_isSharedCheck_1344_ == 0 {
                                                    v___x_1339_ = v___x_1332_;
                                                    v_isShared_1340_ = v_isSharedCheck_1344_;
                                                    state = 19;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_1337_);
                                                    crate::leanh::lean_dec(v___x_1332_);
                                                    v___x_1339_ = crate::leanh::lean_box(0);
                                                    v_isShared_1340_ = v_isSharedCheck_1344_;
                                                    state = 19;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_v_1309_);
                                crate::leanh::lean_dec_ref(v___x_1307_);
                                crate::leanh::lean_dec_ref(v___f_1306_);
                                v___x_1345_ = crate::leanh::lean_box(0);
                                v___x_1346_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___lam__0(v_fst_1304_, v___x_1345_, v_a_1135_, v_snd_1305_, v_a_1137_, v_a_1138_);
                                v___y_1148_ = v___x_1346_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_1148_ = v___x_1302_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1134_);
                    v_val_1347_ = crate::leanh::lean_ctor_get(v___x_1152_, 0);
                    v_isSharedCheck_1355_ = (!crate::leanh::lean_is_exclusive(v___x_1152_)) as u8;
                    if v_isSharedCheck_1355_ == 0 {
                        v___x_1349_ = v___x_1152_;
                        v_isShared_1350_ = v_isSharedCheck_1355_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1347_);
                        crate::leanh::lean_dec(v___x_1152_);
                        v___x_1349_ = crate::leanh::lean_box(0);
                        v_isShared_1350_ = v_isSharedCheck_1355_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1143_ = lean_st_ref_take(v_a_1135_);
                v___x_1144_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v___x_1143_, v_e_1134_, v_fst_1142_);
                v___x_1145_ = lean_st_ref_set(v_a_1135_, v___x_1144_);
                v___x_1146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1146_, 0, v_a_1141_);
                return v___x_1146_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1148_) == 0 {
                    v_a_1149_ = crate::leanh::lean_ctor_get(v___y_1148_, 0);
                    crate::leanh::lean_inc(v_a_1149_);
                    crate::leanh::lean_dec_ref_known(v___y_1148_, 1);
                    v_fst_1150_ = crate::leanh::lean_ctor_get(v_a_1149_, 0);
                    crate::leanh::lean_inc(v_fst_1150_);
                    v_a_1141_ = v_a_1149_;
                    v_fst_1142_ = v_fst_1150_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_1134_);
                    return v___y_1148_;
                }
            }
            3 => {
                v___x_1175_ = l_Lean_Expr_forallE___override(
                    v_fst_1170_,
                    v_fst_1162_,
                    v_fst_1167_,
                    v_binderInfo_1159_,
                );
                crate::leanh::lean_inc_ref(v___x_1175_);
                if v_isShared_1174_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1173_, 0, v___x_1175_);
                    v___x_1177_ = v___x_1173_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_snd_1171_);
                    v___x_1177_ = v_reuseFailAlloc_1178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_1141_ = v___x_1177_;
                v_fst_1142_ = v___x_1175_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1199_ = l_Lean_Expr_lam___override(
                    v_fst_1194_,
                    v_fst_1186_,
                    v_fst_1191_,
                    v_binderInfo_1183_,
                );
                crate::leanh::lean_inc_ref(v___x_1199_);
                if v_isShared_1198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1197_, 0, v___x_1199_);
                    v___x_1201_ = v___x_1197_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_snd_1195_);
                    v___x_1201_ = v_reuseFailAlloc_1202_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_1141_ = v___x_1201_;
                v_fst_1142_ = v___x_1199_;
                state = 1;
                continue;
            }
            7 => {
                v___x_1228_ = l_Lean_Expr_letE___override(
                    v_fst_1223_,
                    v_fst_1211_,
                    v_fst_1215_,
                    v_fst_1220_,
                    v_nondep_1208_,
                );
                crate::leanh::lean_inc_ref(v___x_1228_);
                if v_isShared_1227_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1228_);
                    v___x_1230_ = v___x_1226_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_snd_1224_);
                    v___x_1230_ = v_reuseFailAlloc_1231_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_1141_ = v___x_1230_;
                v_fst_1142_ = v___x_1228_;
                state = 1;
                continue;
            }
            9 => {
                v___x_1254_ = lean_ptr_addr(v_fn_1233_);
                v___x_1255_ = lean_ptr_addr(v_fst_1237_);
                v___x_1256_ = lean_usize_dec_eq(v___x_1254_, v___x_1255_);
                if v___x_1256_ == 0 {
                    v___y_1252_ = v___x_1256_;
                    state = 12;
                    continue;
                } else {
                    v___x_1257_ = lean_ptr_addr(v_arg_1234_);
                    v___x_1258_ = lean_ptr_addr(v_fst_1241_);
                    v___x_1259_ = lean_usize_dec_eq(v___x_1257_, v___x_1258_);
                    v___y_1252_ = v___x_1259_;
                    state = 12;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_inc_ref(v___y_1247_);
                if v_isShared_1245_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1244_, 0, v___y_1247_);
                    v___x_1249_ = v___x_1244_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___y_1247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_snd_1242_);
                    v___x_1249_ = v_reuseFailAlloc_1250_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_1141_ = v___x_1249_;
                v_fst_1142_ = v___y_1247_;
                state = 1;
                continue;
            }
            12 => {
                if v___y_1252_ == 0 {
                    v___x_1253_ = l_Lean_Expr_app___override(v_fst_1237_, v_fst_1241_);
                    v___y_1247_ = v___x_1253_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1241_);
                    crate::leanh::lean_dec(v_fst_1237_);
                    crate::leanh::lean_inc_ref(v_e_1134_);
                    v___y_1247_ = v_e_1134_;
                    state = 10;
                    continue;
                }
            }
            13 => {
                v___x_1275_ = lean_ptr_addr(v_expr_1262_);
                v___x_1276_ = lean_ptr_addr(v_fst_1265_);
                v___x_1277_ = lean_usize_dec_eq(v___x_1275_, v___x_1276_);
                if v___x_1277_ == 0 {
                    crate::leanh::lean_inc(v_data_1261_);
                    v___x_1278_ = l_Lean_Expr_mdata___override(v_data_1261_, v_fst_1265_);
                    v___y_1271_ = v___x_1278_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1265_);
                    crate::leanh::lean_inc_ref(v_e_1134_);
                    v___y_1271_ = v_e_1134_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_inc_ref(v___y_1271_);
                if v_isShared_1269_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1268_, 0, v___y_1271_);
                    v___x_1273_ = v___x_1268_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___y_1271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_snd_1266_);
                    v___x_1273_ = v_reuseFailAlloc_1274_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_a_1141_ = v___x_1273_;
                v_fst_1142_ = v___y_1271_;
                state = 1;
                continue;
            }
            16 => {
                v___x_1295_ = lean_ptr_addr(v_struct_1282_);
                v___x_1296_ = lean_ptr_addr(v_fst_1285_);
                v___x_1297_ = lean_usize_dec_eq(v___x_1295_, v___x_1296_);
                if v___x_1297_ == 0 {
                    crate::leanh::lean_inc(v_idx_1281_);
                    crate::leanh::lean_inc(v_typeName_1280_);
                    v___x_1298_ =
                        l_Lean_Expr_proj___override(v_typeName_1280_, v_idx_1281_, v_fst_1285_);
                    v___y_1291_ = v___x_1298_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1285_);
                    crate::leanh::lean_inc_ref(v_e_1134_);
                    v___y_1291_ = v_e_1134_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                crate::leanh::lean_inc_ref(v___y_1291_);
                if v_isShared_1289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1288_, 0, v___y_1291_);
                    v___x_1293_ = v___x_1288_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1294_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___y_1291_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_snd_1286_);
                    v___x_1293_ = v_reuseFailAlloc_1294_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v_a_1141_ = v___x_1293_;
                v_fst_1142_ = v___y_1291_;
                state = 1;
                continue;
            }
            19 => {
                if v_isShared_1340_ == 0 {
                    v___x_1342_ = v___x_1339_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1343_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
                    v___x_1342_ = v_reuseFailAlloc_1343_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1342_;
            }
            21 => {
                v___x_1351_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1351_, 0, v_val_1347_);
                crate::leanh::lean_ctor_set(v___x_1351_, 1, v_a_1136_);
                if v_isShared_1350_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1349_, 0);
                    crate::leanh::lean_ctor_set(v___x_1349_, 0, v___x_1351_);
                    v___x_1353_ = v___x_1349_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1354_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
                    v___x_1353_ = v_reuseFailAlloc_1354_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1353_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go___boxed(
    mut v_e_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_a_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(
        v_e_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_,
    );
    crate::leanh::lean_dec(v_a_1360_);
    crate::leanh::lean_dec_ref(v_a_1359_);
    crate::leanh::lean_dec(v_a_1357_);
    return v_res_1362_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0(
    mut v_00_u03b2_1363_: *mut crate::leanh::LeanObject,
    mut v_m_1364_: *mut crate::leanh::LeanObject,
    mut v_a_1365_: *mut crate::leanh::LeanObject,
    mut v_b_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1367_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0___redArg(v_m_1364_, v_a_1365_, v_b_1366_);
    return v___x_1367_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(
    mut v_00_u03b2_1368_: *mut crate::leanh::LeanObject,
    mut v_m_1369_: *mut crate::leanh::LeanObject,
    mut v_a_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___redArg(v_m_1369_, v_a_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1___boxed(
    mut v_00_u03b2_1372_: *mut crate::leanh::LeanObject,
    mut v_m_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1(v_00_u03b2_1372_, v_m_1373_, v_a_1374_);
    crate::leanh::lean_dec_ref(v_a_1374_);
    crate::leanh::lean_dec_ref(v_m_1373_);
    return v_res_1375_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(
    mut v_00_u03b2_1376_: *mut crate::leanh::LeanObject,
    mut v_a_1377_: *mut crate::leanh::LeanObject,
    mut v_x_1378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1379_: u8 = 0;
    v___x_1379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___redArg(v_a_1377_, v_x_1378_);
    return v___x_1379_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_x_1382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1383_: u8 = 0;
    let mut v_r_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1383_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__0(v_00_u03b2_1380_, v_a_1381_, v_x_1382_);
    crate::leanh::lean_dec(v_x_1382_);
    crate::leanh::lean_dec_ref(v_a_1381_);
    v_r_1384_ = crate::leanh::lean_box((v_res_1383_) as usize);
    return v_r_1384_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1(
    mut v_00_u03b2_1385_: *mut crate::leanh::LeanObject,
    mut v_data_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1___redArg(v_data_1386_);
    return v___x_1387_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2(
    mut v_00_u03b2_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_b_1390_: *mut crate::leanh::LeanObject,
    mut v_x_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__2___redArg(v_a_1389_, v_b_1390_, v_x_1391_);
    return v___x_1392_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4(
    mut v_00_u03b2_1393_: *mut crate::leanh::LeanObject,
    mut v_a_1394_: *mut crate::leanh::LeanObject,
    mut v_x_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___redArg(v_a_1394_, v_x_1395_);
    return v___x_1396_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4___boxed(
    mut v_00_u03b2_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_x_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__1_spec__4(v_00_u03b2_1397_, v_a_1398_, v_x_1399_);
    crate::leanh::lean_dec(v_x_1399_);
    crate::leanh::lean_dec_ref(v_a_1398_);
    return v_res_1400_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3(
    mut v_00_u03b2_1401_: *mut crate::leanh::LeanObject,
    mut v_i_1402_: *mut crate::leanh::LeanObject,
    mut v_source_1403_: *mut crate::leanh::LeanObject,
    mut v_target_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3___redArg(v_i_1402_, v_source_1403_, v_target_1404_);
    return v___x_1405_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b2_1406_: *mut crate::leanh::LeanObject,
    mut v_x_1407_: *mut crate::leanh::LeanObject,
    mut v_x_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go_spec__0_spec__1_spec__3_spec__5___redArg(v_x_1407_, v_x_1408_);
    return v___x_1409_;
}
pub unsafe fn _init_l_Lean_Expr_resolveBinderNameHint___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = crate::leanh::lean_box(0);
    v___x_1411_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1412_ = lean_mk_array(v___x_1411_, v___x_1410_);
    return v___x_1412_;
}
pub unsafe fn _init_l_Lean_Expr_resolveBinderNameHint___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_resolveBinderNameHint___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_resolveBinderNameHint___closed__0_once),
        _init_l_Lean_Expr_resolveBinderNameHint___closed__0,
    );
    v___x_1414_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1415_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1415_, 0, v___x_1414_);
    crate::leanh::lean_ctor_set(v___x_1415_, 1, v___x_1413_);
    return v___x_1415_;
}
pub unsafe fn l_Lean_Expr_resolveBinderNameHint(
    mut v_e_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v_fst_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1435_: u8 = 0;
    let mut v_a_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1422_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Expr_resolveBinderNameHint___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Expr_resolveBinderNameHint___closed__1_once),
                    _init_l_Lean_Expr_resolveBinderNameHint___closed__1,
                );
                v___x_1423_ = lean_st_mk_ref(v___x_1422_);
                v___x_1424_ = l_Lean_Expr_resolveBinderNameHint___closed__2;
                v___x_1425_ =
                    l___private_Lean_Meta_BinderNameHint_0__Lean_Expr_resolveBinderNameHint_go(
                        v_e_1418_,
                        v___x_1423_,
                        v___x_1424_,
                        v_a_1419_,
                        v_a_1420_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1425_) == 0 {
                    v_a_1426_ = crate::leanh::lean_ctor_get(v___x_1425_, 0);
                    v_isSharedCheck_1435_ = (!crate::leanh::lean_is_exclusive(v___x_1425_)) as u8;
                    if v_isSharedCheck_1435_ == 0 {
                        v___x_1428_ = v___x_1425_;
                        v_isShared_1429_ = v_isSharedCheck_1435_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1426_);
                        crate::leanh::lean_dec(v___x_1425_);
                        v___x_1428_ = crate::leanh::lean_box(0);
                        v_isShared_1429_ = v_isSharedCheck_1435_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1423_);
                    v_a_1436_ = crate::leanh::lean_ctor_get(v___x_1425_, 0);
                    v_isSharedCheck_1443_ = (!crate::leanh::lean_is_exclusive(v___x_1425_)) as u8;
                    if v_isSharedCheck_1443_ == 0 {
                        v___x_1438_ = v___x_1425_;
                        v_isShared_1439_ = v_isSharedCheck_1443_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1436_);
                        crate::leanh::lean_dec(v___x_1425_);
                        v___x_1438_ = crate::leanh::lean_box(0);
                        v_isShared_1439_ = v_isSharedCheck_1443_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1430_ = crate::leanh::lean_ctor_get(v_a_1426_, 0);
                crate::leanh::lean_inc(v_fst_1430_);
                crate::leanh::lean_dec(v_a_1426_);
                v___x_1431_ = lean_st_ref_get(v___x_1423_);
                crate::leanh::lean_dec(v___x_1423_);
                crate::leanh::lean_dec(v___x_1431_);
                if v_isShared_1429_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1428_, 0, v_fst_1430_);
                    v___x_1433_ = v___x_1428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1434_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_fst_1430_);
                    v___x_1433_ = v_reuseFailAlloc_1434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1433_;
            }
            3 => {
                if v_isShared_1439_ == 0 {
                    v___x_1441_ = v___x_1438_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
                    v___x_1441_ = v_reuseFailAlloc_1442_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_resolveBinderNameHint___boxed(
    mut v_e_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
    mut v_a_1446_: *mut crate::leanh::LeanObject,
    mut v_a_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1448_ = l_Lean_Expr_resolveBinderNameHint(v_e_1444_, v_a_1445_, v_a_1446_);
    crate::leanh::lean_dec(v_a_1446_);
    crate::leanh::lean_dec_ref(v_a_1445_);
    return v_res_1448_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_BinderNameHint(
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
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_BinderNameHint(
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
pub unsafe fn initialize_Lean_Meta_BinderNameHint(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Meta_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_BinderNameHint(builtin);
}
