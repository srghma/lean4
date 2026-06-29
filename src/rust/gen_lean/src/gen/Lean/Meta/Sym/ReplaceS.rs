// Lean compiler output
// Module: Lean.Meta.Sym.ReplaceS
// Imports: Lean.Meta.Sym.AlphaShareBuilder Init.Omega
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_lift,
    l_StateT_map, l_StateT_pure,
};
use crate::r#gen::Init::Core::l_instBEqProd___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Hashable::l_instHashableProd___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::UInt::BasicAux::l_UInt64_ofNat___boxed;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instMonad___redArg, l_instBEqOfDecidableEq___redArg___lam__0___boxed,
    l_instDecidableEqNat___boxed, l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_empty;
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder,
    l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM,
    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0,
    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1,
    l_Lean_Meta_Sym_Internal_mkAppS___redArg, l_Lean_Meta_Sym_Internal_mkForallS___redArg,
    l_Lean_Meta_Sym_Internal_mkLambdaS___redArg, l_Lean_Meta_Sym_Internal_mkLetS___redArg,
    l_Lean_Meta_Sym_Internal_mkMDataS___redArg, l_Lean_Meta_Sym_Internal_mkProjS___redArg,
    runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareCommon::{
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed,
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1, l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg;
use crate::ffi::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_uint64_mix_hash,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashableProd___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_bind as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_pure as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_map as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34_value:
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
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83,
        121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77,
        101, 116, 97, 46, 83, 121, 109, 46, 118, 105, 115, 105, 116, 0,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99,
        101, 83, 0,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_replaceS_x27___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_replaceS_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_replaceS_x27___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_replaceS_x27___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_replaceS___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_replaceS___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_replaceS___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_replaceS___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_replaceS___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_replaceS___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_replaceS___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_replaceS___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(
    mut v_a_1008_: *mut crate::leanh::LeanObject,
    mut v_x_1009_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1010_: u8 = 0;
    let mut v_key_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1014_: u8 = 0;
    let mut v_fst_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1009_) == 0 {
                    v___x_1010_ = 0;
                    return v___x_1010_;
                } else {
                    v_key_1011_ = crate::leanh::lean_ctor_get(v_x_1009_, 0);
                    v_tail_1012_ = crate::leanh::lean_ctor_get(v_x_1009_, 2);
                    v_fst_1016_ = crate::leanh::lean_ctor_get(v_key_1011_, 0);
                    v_snd_1017_ = crate::leanh::lean_ctor_get(v_key_1011_, 1);
                    v_fst_1018_ = crate::leanh::lean_ctor_get(v_a_1008_, 0);
                    v_snd_1019_ = crate::leanh::lean_ctor_get(v_a_1008_, 1);
                    v___x_1020_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_1016_,
                            v_fst_1018_,
                        );
                    if v___x_1020_ == 0 {
                        v___y_1014_ = v___x_1020_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1021_ = lean_nat_dec_eq(v_snd_1017_, v_snd_1019_);
                        v___y_1014_ = v___x_1021_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1014_ == 0 {
                    v_x_1009_ = v_tail_1012_;
                    state = 0;
                    continue;
                } else {
                    return v___y_1014_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(
    mut v_a_1022_: *mut crate::leanh::LeanObject,
    mut v_x_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1024_: u8 = 0;
    let mut v_r_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1024_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1022_, v_x_1023_);
    crate::leanh::lean_dec(v_x_1023_);
    crate::leanh::lean_dec_ref(v_a_1022_);
    v_r_1025_ = crate::leanh::lean_box((v_res_1024_) as usize);
    return v_r_1025_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1026_: *mut crate::leanh::LeanObject,
    mut v_x_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1033_: u8 = 0;
    let mut v_fst_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: u64 = 0;
    let mut v___x_1038_: u64 = 0;
    let mut v___x_1039_: u64 = 0;
    let mut v___x_1040_: u64 = 0;
    let mut v___x_1041_: u64 = 0;
    let mut v_fold_1042_: u64 = 0;
    let mut v___x_1043_: u64 = 0;
    let mut v___x_1044_: u64 = 0;
    let mut v___x_1045_: u64 = 0;
    let mut v___x_1046_: usize = 0;
    let mut v___x_1047_: usize = 0;
    let mut v___x_1048_: usize = 0;
    let mut v___x_1049_: usize = 0;
    let mut v___x_1050_: usize = 0;
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1027_) == 0 {
                    return v_x_1026_;
                } else {
                    v_key_1028_ = crate::leanh::lean_ctor_get(v_x_1027_, 0);
                    v_value_1029_ = crate::leanh::lean_ctor_get(v_x_1027_, 1);
                    v_tail_1030_ = crate::leanh::lean_ctor_get(v_x_1027_, 2);
                    v_isSharedCheck_1057_ = (!crate::leanh::lean_is_exclusive(v_x_1027_)) as u8;
                    if v_isSharedCheck_1057_ == 0 {
                        v___x_1032_ = v_x_1027_;
                        v_isShared_1033_ = v_isSharedCheck_1057_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1030_);
                        crate::leanh::lean_inc(v_value_1029_);
                        crate::leanh::lean_inc(v_key_1028_);
                        crate::leanh::lean_dec(v_x_1027_);
                        v___x_1032_ = crate::leanh::lean_box(0);
                        v_isShared_1033_ = v_isSharedCheck_1057_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1034_ = crate::leanh::lean_ctor_get(v_key_1028_, 0);
                v_snd_1035_ = crate::leanh::lean_ctor_get(v_key_1028_, 1);
                v___x_1036_ = lean_array_get_size(v_x_1026_);
                v___x_1037_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1034_);
                v___x_1038_ = lean_uint64_of_nat(v_snd_1035_);
                v___x_1039_ = lean_uint64_mix_hash(v___x_1037_, v___x_1038_);
                v___x_1040_ = 32u64;
                v___x_1041_ = lean_uint64_shift_right(v___x_1039_, v___x_1040_);
                v_fold_1042_ = lean_uint64_xor(v___x_1039_, v___x_1041_);
                v___x_1043_ = 16u64;
                v___x_1044_ = lean_uint64_shift_right(v_fold_1042_, v___x_1043_);
                v___x_1045_ = lean_uint64_xor(v_fold_1042_, v___x_1044_);
                v___x_1046_ = lean_uint64_to_usize(v___x_1045_);
                v___x_1047_ = lean_usize_of_nat(v___x_1036_);
                v___x_1048_ = 1usize;
                v___x_1049_ = lean_usize_sub(v___x_1047_, v___x_1048_);
                v___x_1050_ = lean_usize_land(v___x_1046_, v___x_1049_);
                v___x_1051_ = lean_array_uget_borrowed(v_x_1026_, v___x_1050_);
                crate::leanh::lean_inc(v___x_1051_);
                if v_isShared_1033_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1032_, 2, v___x_1051_);
                    v___x_1053_ = v___x_1032_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1056_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_key_1028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_value_1029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1056_, 2, v___x_1051_);
                    v___x_1053_ = v_reuseFailAlloc_1056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1054_ = lean_array_uset(v_x_1026_, v___x_1050_, v___x_1053_);
                v_x_1026_ = v___x_1054_;
                v_x_1027_ = v_tail_1030_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(
    mut v_i_1058_: *mut crate::leanh::LeanObject,
    mut v_source_1059_: *mut crate::leanh::LeanObject,
    mut v_target_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: u8 = 0;
    let mut v_es_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1061_ = lean_array_get_size(v_source_1059_);
                v___x_1062_ = lean_nat_dec_lt(v_i_1058_, v___x_1061_);
                if v___x_1062_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1059_);
                    crate::leanh::lean_dec(v_i_1058_);
                    return v_target_1060_;
                } else {
                    v_es_1063_ = lean_array_fget(v_source_1059_, v_i_1058_);
                    v___x_1064_ = crate::leanh::lean_box(0);
                    v_source_1065_ = lean_array_fset(v_source_1059_, v_i_1058_, v___x_1064_);
                    v_target_1066_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1060_, v_es_1063_);
                    v___x_1067_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1068_ = lean_nat_add(v_i_1058_, v___x_1067_);
                    crate::leanh::lean_dec(v_i_1058_);
                    v_i_1058_ = v___x_1068_;
                    v_source_1059_ = v_source_1065_;
                    v_target_1060_ = v_target_1066_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(
    mut v_data_1070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = lean_array_get_size(v_data_1070_);
    v___x_1072_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1073_ = lean_nat_mul(v___x_1071_, v___x_1072_);
    v___x_1074_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1075_ = crate::leanh::lean_box(0);
    v___x_1076_ = lean_mk_array(v_nbuckets_1073_, v___x_1075_);
    v___x_1077_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1074_, v_data_1070_, v___x_1076_);
    return v___x_1077_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(
    mut v_a_1078_: *mut crate::leanh::LeanObject,
    mut v_b_1079_: *mut crate::leanh::LeanObject,
    mut v_x_1080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1086_: u8 = 0;
    let mut v___y_1088_: u8 = 0;
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: u8 = 0;
    let mut v___x_1101_: u8 = 0;
    let mut v_isSharedCheck_1102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1080_) == 0 {
                    crate::leanh::lean_dec(v_b_1079_);
                    crate::leanh::lean_dec_ref(v_a_1078_);
                    return v_x_1080_;
                } else {
                    v_key_1081_ = crate::leanh::lean_ctor_get(v_x_1080_, 0);
                    v_value_1082_ = crate::leanh::lean_ctor_get(v_x_1080_, 1);
                    v_tail_1083_ = crate::leanh::lean_ctor_get(v_x_1080_, 2);
                    v_isSharedCheck_1102_ = (!crate::leanh::lean_is_exclusive(v_x_1080_)) as u8;
                    if v_isSharedCheck_1102_ == 0 {
                        v___x_1085_ = v_x_1080_;
                        v_isShared_1086_ = v_isSharedCheck_1102_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1083_);
                        crate::leanh::lean_inc(v_value_1082_);
                        crate::leanh::lean_inc(v_key_1081_);
                        crate::leanh::lean_dec(v_x_1080_);
                        v___x_1085_ = crate::leanh::lean_box(0);
                        v_isShared_1086_ = v_isSharedCheck_1102_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1096_ = crate::leanh::lean_ctor_get(v_key_1081_, 0);
                v_snd_1097_ = crate::leanh::lean_ctor_get(v_key_1081_, 1);
                v_fst_1098_ = crate::leanh::lean_ctor_get(v_a_1078_, 0);
                v_snd_1099_ = crate::leanh::lean_ctor_get(v_a_1078_, 1);
                v___x_1100_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fst_1096_,
                        v_fst_1098_,
                    );
                if v___x_1100_ == 0 {
                    v___y_1088_ = v___x_1100_;
                    state = 2;
                    continue;
                } else {
                    v___x_1101_ = lean_nat_dec_eq(v_snd_1097_, v_snd_1099_);
                    v___y_1088_ = v___x_1101_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_1088_ == 0 {
                    v___x_1089_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1078_, v_b_1079_, v_tail_1083_);
                    if v_isShared_1086_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1085_, 2, v___x_1089_);
                        v___x_1091_ = v___x_1085_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1092_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_key_1081_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_value_1082_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1092_, 2, v___x_1089_);
                        v___x_1091_ = v_reuseFailAlloc_1092_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1082_);
                    crate::leanh::lean_dec(v_key_1081_);
                    if v_isShared_1086_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1085_, 1, v_b_1079_);
                        crate::leanh::lean_ctor_set(v___x_1085_, 0, v_a_1078_);
                        v___x_1094_ = v___x_1085_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1095_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1078_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_b_1079_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_tail_1083_);
                        v___x_1094_ = v_reuseFailAlloc_1095_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1091_;
            }
            4 => {
                return v___x_1094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(
    mut v_m_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
    mut v_b_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v_fst_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: u64 = 0;
    let mut v___x_1115_: u64 = 0;
    let mut v___x_1116_: u64 = 0;
    let mut v___x_1117_: u64 = 0;
    let mut v___x_1118_: u64 = 0;
    let mut v_fold_1119_: u64 = 0;
    let mut v___x_1120_: u64 = 0;
    let mut v___x_1121_: u64 = 0;
    let mut v___x_1122_: u64 = 0;
    let mut v___x_1123_: usize = 0;
    let mut v___x_1124_: usize = 0;
    let mut v___x_1125_: usize = 0;
    let mut v___x_1126_: usize = 0;
    let mut v___x_1127_: usize = 0;
    let mut v_bkt_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: u8 = 0;
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: u8 = 0;
    let mut v_val_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1106_ = crate::leanh::lean_ctor_get(v_m_1103_, 0);
                v_buckets_1107_ = crate::leanh::lean_ctor_get(v_m_1103_, 1);
                v_isSharedCheck_1154_ = (!crate::leanh::lean_is_exclusive(v_m_1103_)) as u8;
                if v_isSharedCheck_1154_ == 0 {
                    v___x_1109_ = v_m_1103_;
                    v_isShared_1110_ = v_isSharedCheck_1154_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1107_);
                    crate::leanh::lean_inc(v_size_1106_);
                    crate::leanh::lean_dec(v_m_1103_);
                    v___x_1109_ = crate::leanh::lean_box(0);
                    v_isShared_1110_ = v_isSharedCheck_1154_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1111_ = crate::leanh::lean_ctor_get(v_a_1104_, 0);
                v_snd_1112_ = crate::leanh::lean_ctor_get(v_a_1104_, 1);
                v___x_1113_ = lean_array_get_size(v_buckets_1107_);
                v___x_1114_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1111_);
                v___x_1115_ = lean_uint64_of_nat(v_snd_1112_);
                v___x_1116_ = lean_uint64_mix_hash(v___x_1114_, v___x_1115_);
                v___x_1117_ = 32u64;
                v___x_1118_ = lean_uint64_shift_right(v___x_1116_, v___x_1117_);
                v_fold_1119_ = lean_uint64_xor(v___x_1116_, v___x_1118_);
                v___x_1120_ = 16u64;
                v___x_1121_ = lean_uint64_shift_right(v_fold_1119_, v___x_1120_);
                v___x_1122_ = lean_uint64_xor(v_fold_1119_, v___x_1121_);
                v___x_1123_ = lean_uint64_to_usize(v___x_1122_);
                v___x_1124_ = lean_usize_of_nat(v___x_1113_);
                v___x_1125_ = 1usize;
                v___x_1126_ = lean_usize_sub(v___x_1124_, v___x_1125_);
                v___x_1127_ = lean_usize_land(v___x_1123_, v___x_1126_);
                v_bkt_1128_ = lean_array_uget_borrowed(v_buckets_1107_, v___x_1127_);
                v___x_1129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1104_, v_bkt_1128_);
                if v___x_1129_ == 0 {
                    v___x_1130_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1131_ = lean_nat_add(v_size_1106_, v___x_1130_);
                    crate::leanh::lean_dec(v_size_1106_);
                    crate::leanh::lean_inc(v_bkt_1128_);
                    v___x_1132_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1132_, 0, v_a_1104_);
                    crate::leanh::lean_ctor_set(v___x_1132_, 1, v_b_1105_);
                    crate::leanh::lean_ctor_set(v___x_1132_, 2, v_bkt_1128_);
                    v_buckets_x27_1133_ =
                        lean_array_uset(v_buckets_1107_, v___x_1127_, v___x_1132_);
                    v___x_1134_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1135_ = lean_nat_mul(v_size_x27_1131_, v___x_1134_);
                    v___x_1136_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1137_ = lean_nat_div(v___x_1135_, v___x_1136_);
                    crate::leanh::lean_dec(v___x_1135_);
                    v___x_1138_ = lean_array_get_size(v_buckets_x27_1133_);
                    v___x_1139_ = lean_nat_dec_le(v___x_1137_, v___x_1138_);
                    crate::leanh::lean_dec(v___x_1137_);
                    if v___x_1139_ == 0 {
                        v_val_1140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1133_);
                        if v_isShared_1110_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1109_, 1, v_val_1140_);
                            crate::leanh::lean_ctor_set(v___x_1109_, 0, v_size_x27_1131_);
                            v___x_1142_ = v___x_1109_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1143_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1143_,
                                0,
                                v_size_x27_1131_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_val_1140_);
                            v___x_1142_ = v_reuseFailAlloc_1143_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1110_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1109_, 1, v_buckets_x27_1133_);
                            crate::leanh::lean_ctor_set(v___x_1109_, 0, v_size_x27_1131_);
                            v___x_1145_ = v___x_1109_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1146_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1146_,
                                0,
                                v_size_x27_1131_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1146_,
                                1,
                                v_buckets_x27_1133_,
                            );
                            v___x_1145_ = v_reuseFailAlloc_1146_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1128_);
                    v___x_1147_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1148_ =
                        lean_array_uset(v_buckets_1107_, v___x_1127_, v___x_1147_);
                    v___x_1149_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1104_, v_b_1105_, v_bkt_1128_);
                    v___x_1150_ = lean_array_uset(v_buckets_x27_1148_, v___x_1127_, v___x_1149_);
                    if v_isShared_1110_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1109_, 1, v___x_1150_);
                        v___x_1152_ = v___x_1109_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1153_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_size_1106_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
                        v___x_1152_ = v_reuseFailAlloc_1153_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1142_;
            }
            3 => {
                return v___x_1145_;
            }
            4 => {
                return v___x_1152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
    mut v_key_1155_: *mut crate::leanh::LeanObject,
    mut v_r_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
    mut v_a_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_r_1156_);
    v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1157_, v_key_1155_, v_r_1156_);
    v___x_1160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1160_, 0, v_r_1156_);
    crate::leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    v___x_1161_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1161_, 0, v___x_1160_);
    crate::leanh::lean_ctor_set(v___x_1161_, 1, v_a_1158_);
    return v___x_1161_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
    mut v_key_1162_: *mut crate::leanh::LeanObject,
    mut v_r_1163_: *mut crate::leanh::LeanObject,
    mut v_a_1164_: *mut crate::leanh::LeanObject,
    mut v_a_1165_: u8,
    mut v_a_1166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1167_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
        v_key_1162_,
        v_r_1163_,
        v_a_1164_,
        v_a_1166_,
    );
    return v___x_1167_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(
    mut v_key_1168_: *mut crate::leanh::LeanObject,
    mut v_r_1169_: *mut crate::leanh::LeanObject,
    mut v_a_1170_: *mut crate::leanh::LeanObject,
    mut v_a_1171_: *mut crate::leanh::LeanObject,
    mut v_a_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1173_: u8 = 0;
    let mut v_res_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1173_ = (crate::leanh::lean_unbox(v_a_1171_) as u8);
    v_res_1174_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
        v_key_1168_,
        v_r_1169_,
        v_a_1170_,
        v_a_boxed_1173_,
        v_a_1172_,
    );
    return v_res_1174_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(
    mut v_00_u03b2_1175_: *mut crate::leanh::LeanObject,
    mut v_m_1176_: *mut crate::leanh::LeanObject,
    mut v_a_1177_: *mut crate::leanh::LeanObject,
    mut v_b_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1179_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1176_, v_a_1177_, v_b_1178_);
    return v___x_1179_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(
    mut v_00_u03b2_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_x_1182_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1183_: u8 = 0;
    v___x_1183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1181_, v_x_1182_);
    return v___x_1183_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(
    mut v_00_u03b2_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v_x_1186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1187_: u8 = 0;
    let mut v_r_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1187_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1184_, v_a_1185_, v_x_1186_);
    crate::leanh::lean_dec(v_x_1186_);
    crate::leanh::lean_dec_ref(v_a_1185_);
    v_r_1188_ = crate::leanh::lean_box((v_res_1187_) as usize);
    return v_r_1188_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1(
    mut v_00_u03b2_1189_: *mut crate::leanh::LeanObject,
    mut v_data_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1190_);
    return v___x_1191_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2(
    mut v_00_u03b2_1192_: *mut crate::leanh::LeanObject,
    mut v_a_1193_: *mut crate::leanh::LeanObject,
    mut v_b_1194_: *mut crate::leanh::LeanObject,
    mut v_x_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1196_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1193_, v_b_1194_, v_x_1195_);
    return v___x_1196_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1197_: *mut crate::leanh::LeanObject,
    mut v_i_1198_: *mut crate::leanh::LeanObject,
    mut v_source_1199_: *mut crate::leanh::LeanObject,
    mut v_target_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1198_, v_source_1199_, v_target_1200_);
    return v___x_1201_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1202_: *mut crate::leanh::LeanObject,
    mut v_x_1203_: *mut crate::leanh::LeanObject,
    mut v_x_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1205_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1203_, v_x_1204_);
    return v___x_1205_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqNat___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1213_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1213_, 0, v___x_1212_);
    return v___f_1213_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1214_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4,
    );
    v___f_1215_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0;
    v___f_1216_ = crate::leanh::lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1216_, 0, v___f_1215_);
    crate::leanh::lean_closure_set(v___f_1216_, 1, v___f_1214_);
    return v___f_1216_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1262_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19;
    v___x_1263_ = l_ReaderT_instMonad___redArg(v___x_1262_);
    return v___x_1263_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1264_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___x_1265_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1265_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1265_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1265_, 2, v___x_1264_);
    return v___x_1265_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___f_1267_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1267_, 0, v___x_1266_);
    return v___f_1267_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1268_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___f_1269_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1269_, 0, v___x_1268_);
    return v___f_1269_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1270_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___f_1271_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1271_, 0, v___x_1270_);
    return v___f_1271_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___x_1273_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1273_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1273_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1273_, 2, v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___f_1275_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1275_, 0, v___x_1274_);
    return v___f_1275_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___x_1277_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1277_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1277_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1277_, 2, v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1278_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21,
    );
    v___x_1279_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25,
    );
    v___x_1280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1280_, 0, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1280_, 1, v___f_1278_);
    return v___x_1280_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1281_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24,
    );
    v___f_1282_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23,
    );
    v___f_1283_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22,
    );
    v___x_1284_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27,
    );
    v___x_1285_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26,
    );
    v___x_1286_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1286_, 0, v___x_1285_);
    crate::leanh::lean_ctor_set(v___x_1286_, 1, v___x_1284_);
    crate::leanh::lean_ctor_set(v___x_1286_, 2, v___f_1283_);
    crate::leanh::lean_ctor_set(v___x_1286_, 3, v___f_1282_);
    crate::leanh::lean_ctor_set(v___x_1286_, 4, v___f_1281_);
    return v___x_1286_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29,
    );
    v___x_1288_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28,
    );
    v___x_1289_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1288_);
    crate::leanh::lean_ctor_set(v___x_1289_, 1, v___x_1287_);
    return v___x_1289_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___x_1291_ = crate::leanh::lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1291_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1291_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1291_, 2, v___x_1290_);
    return v___x_1291_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1292_ = l_Lean_instInhabitedExpr;
    v___x_1293_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30,
    );
    v___x_1294_ = l_instInhabitedOfMonad___redArg(v___x_1293_, v___x_1292_);
    return v___x_1294_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1298_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35;
    v___x_1299_ = crate::leanh::lean_unsigned_to_nat(67);
    v___x_1300_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_1301_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34;
    v___x_1302_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33;
    v___x_1303_ = l_mkPanicMessageWithDecl(
        v___x_1302_,
        v___x_1301_,
        v___x_1300_,
        v___x_1299_,
        v___x_1298_,
    );
    return v___x_1303_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(
    mut v_e_1304_: *mut crate::leanh::LeanObject,
    mut v_offset_1305_: *mut crate::leanh::LeanObject,
    mut v_fn_1306_: *mut crate::leanh::LeanObject,
    mut v_a_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: u8,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share1_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assertShared_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v_fst_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v___y_1340_: u8 = 0;
    let mut v___x_10643__overap_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: u8 = 0;
    let mut v___x_1351_: u8 = 0;
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut v_binderName_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1357_: u8 = 0;
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v_fst_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___y_1377_: u8 = 0;
    let mut v___x_10804__overap_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: u8 = 0;
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut v_binderName_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1394_: u8 = 0;
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v_fst_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1412_: u8 = 0;
    let mut v___y_1414_: u8 = 0;
    let mut v___x_10969__overap_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: u8 = 0;
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut v_isSharedCheck_1427_: u8 = 0;
    let mut v_declName_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v_fst_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1455_: u8 = 0;
    let mut v___y_1457_: u8 = 0;
    let mut v___x_11156__overap_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    let mut v___x_11158__overap_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v_isSharedCheck_1473_: u8 = 0;
    let mut v_isSharedCheck_1474_: u8 = 0;
    let mut v_data_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1482_: u8 = 0;
    let mut v_fst_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v___x_1488_: u8 = 0;
    let mut v___x_11315__overap_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut v_isSharedCheck_1499_: u8 = 0;
    let mut v_typeName_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v_fst_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1514_: u8 = 0;
    let mut v___x_11427__overap_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut v_isSharedCheck_1525_: u8 = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10529__overap_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1310_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
                    ),
                    _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
                );
                v___x_1311_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30_once
                    ),
                    _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30,
                );
                v___x_1312_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
                v_share1_1313_ = crate::leanh::lean_ctor_get(v___x_1312_, 0);
                v_assertShared_1314_ = crate::leanh::lean_ctor_get(v___x_1312_, 1);
                v_isDebugEnabled_1315_ = crate::leanh::lean_ctor_get(v___x_1312_, 2);
                v___x_1316_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31_once
                    ),
                    _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31,
                );
                crate::leanh::lean_inc(v_share1_1313_);
                v___f_1317_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1317_, 0, v_share1_1313_);
                crate::leanh::lean_closure_set(v___f_1317_, 1, v___x_1316_);
                crate::leanh::lean_inc(v_assertShared_1314_);
                v___f_1318_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1318_, 0, v_assertShared_1314_);
                crate::leanh::lean_closure_set(v___f_1318_, 1, v___x_1316_);
                crate::leanh::lean_inc(v_isDebugEnabled_1315_);
                v___x_1319_ =
                    crate::leanh::lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 5);
                crate::leanh::lean_closure_set(v___x_1319_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1319_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1319_, 2, v___x_1310_);
                crate::leanh::lean_closure_set(v___x_1319_, 3, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1319_, 4, v_isDebugEnabled_1315_);
                v___x_1320_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1320_, 0, v___f_1317_);
                crate::leanh::lean_ctor_set(v___x_1320_, 1, v___f_1318_);
                crate::leanh::lean_ctor_set(v___x_1320_, 2, v___x_1319_);
                match crate::leanh::lean_obj_tag(v_e_1304_) {
                    5 => {
                        v_fn_1321_ = crate::leanh::lean_ctor_get(v_e_1304_, 0);
                        v_arg_1322_ = crate::leanh::lean_ctor_get(v_e_1304_, 1);
                        crate::leanh::lean_inc_ref(v_fn_1306_);
                        crate::leanh::lean_inc(v_offset_1305_);
                        crate::leanh::lean_inc_ref(v_fn_1321_);
                        v___x_1323_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_fn_1321_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1324_ = crate::leanh::lean_ctor_get(v___x_1323_, 0);
                        crate::leanh::lean_inc(v_fst_1324_);
                        v_snd_1325_ = crate::leanh::lean_ctor_get(v___x_1323_, 1);
                        crate::leanh::lean_inc(v_snd_1325_);
                        crate::leanh::lean_dec_ref(v___x_1323_);
                        v_fst_1326_ = crate::leanh::lean_ctor_get(v_fst_1324_, 0);
                        crate::leanh::lean_inc(v_fst_1326_);
                        v_snd_1327_ = crate::leanh::lean_ctor_get(v_fst_1324_, 1);
                        crate::leanh::lean_inc(v_snd_1327_);
                        crate::leanh::lean_dec(v_fst_1324_);
                        crate::leanh::lean_inc_ref(v_arg_1322_);
                        v___x_1328_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_arg_1322_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_snd_1327_,
                                v_a_1308_,
                                v_snd_1325_,
                            );
                        v_fst_1329_ = crate::leanh::lean_ctor_get(v___x_1328_, 0);
                        v_snd_1330_ = crate::leanh::lean_ctor_get(v___x_1328_, 1);
                        v_isSharedCheck_1353_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1328_)) as u8;
                        if v_isSharedCheck_1353_ == 0 {
                            v___x_1332_ = v___x_1328_;
                            v_isShared_1333_ = v_isSharedCheck_1353_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1330_);
                            crate::leanh::lean_inc(v_fst_1329_);
                            crate::leanh::lean_dec(v___x_1328_);
                            v___x_1332_ = crate::leanh::lean_box(0);
                            v_isShared_1333_ = v_isSharedCheck_1353_;
                            state = 1;
                            continue;
                        }
                    }
                    6 => {
                        v_binderName_1354_ = crate::leanh::lean_ctor_get(v_e_1304_, 0);
                        v_binderType_1355_ = crate::leanh::lean_ctor_get(v_e_1304_, 1);
                        v_body_1356_ = crate::leanh::lean_ctor_get(v_e_1304_, 2);
                        v_binderInfo_1357_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_1304_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_inc_ref(v_fn_1306_);
                        crate::leanh::lean_inc(v_offset_1305_);
                        crate::leanh::lean_inc_ref(v_binderType_1355_);
                        v___x_1358_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_binderType_1355_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1359_ = crate::leanh::lean_ctor_get(v___x_1358_, 0);
                        crate::leanh::lean_inc(v_fst_1359_);
                        v_snd_1360_ = crate::leanh::lean_ctor_get(v___x_1358_, 1);
                        crate::leanh::lean_inc(v_snd_1360_);
                        crate::leanh::lean_dec_ref(v___x_1358_);
                        v_fst_1361_ = crate::leanh::lean_ctor_get(v_fst_1359_, 0);
                        crate::leanh::lean_inc(v_fst_1361_);
                        v_snd_1362_ = crate::leanh::lean_ctor_get(v_fst_1359_, 1);
                        crate::leanh::lean_inc(v_snd_1362_);
                        crate::leanh::lean_dec(v_fst_1359_);
                        v___x_1363_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1364_ = lean_nat_add(v_offset_1305_, v___x_1363_);
                        crate::leanh::lean_dec(v_offset_1305_);
                        crate::leanh::lean_inc_ref(v_body_1356_);
                        v___x_1365_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_body_1356_,
                                v___x_1364_,
                                v_fn_1306_,
                                v_snd_1362_,
                                v_a_1308_,
                                v_snd_1360_,
                            );
                        v_fst_1366_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                        v_snd_1367_ = crate::leanh::lean_ctor_get(v___x_1365_, 1);
                        v_isSharedCheck_1390_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1365_)) as u8;
                        if v_isSharedCheck_1390_ == 0 {
                            v___x_1369_ = v___x_1365_;
                            v_isShared_1370_ = v_isSharedCheck_1390_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1367_);
                            crate::leanh::lean_inc(v_fst_1366_);
                            crate::leanh::lean_dec(v___x_1365_);
                            v___x_1369_ = crate::leanh::lean_box(0);
                            v_isShared_1370_ = v_isSharedCheck_1390_;
                            state = 6;
                            continue;
                        }
                    }
                    7 => {
                        v_binderName_1391_ = crate::leanh::lean_ctor_get(v_e_1304_, 0);
                        v_binderType_1392_ = crate::leanh::lean_ctor_get(v_e_1304_, 1);
                        v_body_1393_ = crate::leanh::lean_ctor_get(v_e_1304_, 2);
                        v_binderInfo_1394_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_1304_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_inc_ref(v_fn_1306_);
                        crate::leanh::lean_inc(v_offset_1305_);
                        crate::leanh::lean_inc_ref(v_binderType_1392_);
                        v___x_1395_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_binderType_1392_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1396_ = crate::leanh::lean_ctor_get(v___x_1395_, 0);
                        crate::leanh::lean_inc(v_fst_1396_);
                        v_snd_1397_ = crate::leanh::lean_ctor_get(v___x_1395_, 1);
                        crate::leanh::lean_inc(v_snd_1397_);
                        crate::leanh::lean_dec_ref(v___x_1395_);
                        v_fst_1398_ = crate::leanh::lean_ctor_get(v_fst_1396_, 0);
                        crate::leanh::lean_inc(v_fst_1398_);
                        v_snd_1399_ = crate::leanh::lean_ctor_get(v_fst_1396_, 1);
                        crate::leanh::lean_inc(v_snd_1399_);
                        crate::leanh::lean_dec(v_fst_1396_);
                        v___x_1400_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1401_ = lean_nat_add(v_offset_1305_, v___x_1400_);
                        crate::leanh::lean_dec(v_offset_1305_);
                        crate::leanh::lean_inc_ref(v_body_1393_);
                        v___x_1402_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_body_1393_,
                                v___x_1401_,
                                v_fn_1306_,
                                v_snd_1399_,
                                v_a_1308_,
                                v_snd_1397_,
                            );
                        v_fst_1403_ = crate::leanh::lean_ctor_get(v___x_1402_, 0);
                        v_snd_1404_ = crate::leanh::lean_ctor_get(v___x_1402_, 1);
                        v_isSharedCheck_1427_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1402_)) as u8;
                        if v_isSharedCheck_1427_ == 0 {
                            v___x_1406_ = v___x_1402_;
                            v_isShared_1407_ = v_isSharedCheck_1427_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1404_);
                            crate::leanh::lean_inc(v_fst_1403_);
                            crate::leanh::lean_dec(v___x_1402_);
                            v___x_1406_ = crate::leanh::lean_box(0);
                            v_isShared_1407_ = v_isSharedCheck_1427_;
                            state = 11;
                            continue;
                        }
                    }
                    8 => {
                        v_declName_1428_ = crate::leanh::lean_ctor_get(v_e_1304_, 0);
                        v_type_1429_ = crate::leanh::lean_ctor_get(v_e_1304_, 1);
                        v_value_1430_ = crate::leanh::lean_ctor_get(v_e_1304_, 2);
                        v_body_1431_ = crate::leanh::lean_ctor_get(v_e_1304_, 3);
                        v_nondep_1432_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_1304_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                        );
                        crate::leanh::lean_inc_ref_n(v_fn_1306_, 2);
                        crate::leanh::lean_inc_n(v_offset_1305_, 2);
                        crate::leanh::lean_inc_ref(v_type_1429_);
                        v___x_1433_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_type_1429_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1434_ = crate::leanh::lean_ctor_get(v___x_1433_, 0);
                        crate::leanh::lean_inc(v_fst_1434_);
                        v_snd_1435_ = crate::leanh::lean_ctor_get(v___x_1433_, 1);
                        crate::leanh::lean_inc(v_snd_1435_);
                        crate::leanh::lean_dec_ref(v___x_1433_);
                        v_fst_1436_ = crate::leanh::lean_ctor_get(v_fst_1434_, 0);
                        crate::leanh::lean_inc(v_fst_1436_);
                        v_snd_1437_ = crate::leanh::lean_ctor_get(v_fst_1434_, 1);
                        crate::leanh::lean_inc(v_snd_1437_);
                        crate::leanh::lean_dec(v_fst_1434_);
                        crate::leanh::lean_inc_ref(v_value_1430_);
                        v___x_1438_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_value_1430_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_snd_1437_,
                                v_a_1308_,
                                v_snd_1435_,
                            );
                        v_fst_1439_ = crate::leanh::lean_ctor_get(v___x_1438_, 0);
                        crate::leanh::lean_inc(v_fst_1439_);
                        v_snd_1440_ = crate::leanh::lean_ctor_get(v___x_1438_, 1);
                        crate::leanh::lean_inc(v_snd_1440_);
                        crate::leanh::lean_dec_ref(v___x_1438_);
                        v_fst_1441_ = crate::leanh::lean_ctor_get(v_fst_1439_, 0);
                        crate::leanh::lean_inc(v_fst_1441_);
                        v_snd_1442_ = crate::leanh::lean_ctor_get(v_fst_1439_, 1);
                        crate::leanh::lean_inc(v_snd_1442_);
                        crate::leanh::lean_dec(v_fst_1439_);
                        v___x_1443_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1444_ = lean_nat_add(v_offset_1305_, v___x_1443_);
                        crate::leanh::lean_dec(v_offset_1305_);
                        crate::leanh::lean_inc_ref(v_body_1431_);
                        v___x_1445_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_body_1431_,
                                v___x_1444_,
                                v_fn_1306_,
                                v_snd_1442_,
                                v_a_1308_,
                                v_snd_1440_,
                            );
                        v_fst_1446_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                        v_snd_1447_ = crate::leanh::lean_ctor_get(v___x_1445_, 1);
                        v_isSharedCheck_1474_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1445_)) as u8;
                        if v_isSharedCheck_1474_ == 0 {
                            v___x_1449_ = v___x_1445_;
                            v_isShared_1450_ = v_isSharedCheck_1474_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1447_);
                            crate::leanh::lean_inc(v_fst_1446_);
                            crate::leanh::lean_dec(v___x_1445_);
                            v___x_1449_ = crate::leanh::lean_box(0);
                            v_isShared_1450_ = v_isSharedCheck_1474_;
                            state = 16;
                            continue;
                        }
                    }
                    10 => {
                        v_data_1475_ = crate::leanh::lean_ctor_get(v_e_1304_, 0);
                        v_expr_1476_ = crate::leanh::lean_ctor_get(v_e_1304_, 1);
                        crate::leanh::lean_inc_ref(v_expr_1476_);
                        v___x_1477_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_expr_1476_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1478_ = crate::leanh::lean_ctor_get(v___x_1477_, 0);
                        v_snd_1479_ = crate::leanh::lean_ctor_get(v___x_1477_, 1);
                        v_isSharedCheck_1499_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1477_)) as u8;
                        if v_isSharedCheck_1499_ == 0 {
                            v___x_1481_ = v___x_1477_;
                            v_isShared_1482_ = v_isSharedCheck_1499_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1479_);
                            crate::leanh::lean_inc(v_fst_1478_);
                            crate::leanh::lean_dec(v___x_1477_);
                            v___x_1481_ = crate::leanh::lean_box(0);
                            v_isShared_1482_ = v_isSharedCheck_1499_;
                            state = 21;
                            continue;
                        }
                    }
                    11 => {
                        v_typeName_1500_ = crate::leanh::lean_ctor_get(v_e_1304_, 0);
                        v_idx_1501_ = crate::leanh::lean_ctor_get(v_e_1304_, 1);
                        v_struct_1502_ = crate::leanh::lean_ctor_get(v_e_1304_, 2);
                        crate::leanh::lean_inc_ref(v_struct_1502_);
                        v___x_1503_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_struct_1502_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1504_ = crate::leanh::lean_ctor_get(v___x_1503_, 0);
                        v_snd_1505_ = crate::leanh::lean_ctor_get(v___x_1503_, 1);
                        v_isSharedCheck_1525_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1503_)) as u8;
                        if v_isSharedCheck_1525_ == 0 {
                            v___x_1507_ = v___x_1503_;
                            v_isShared_1508_ = v_isSharedCheck_1525_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1505_);
                            crate::leanh::lean_inc(v_fst_1504_);
                            crate::leanh::lean_dec(v___x_1503_);
                            v___x_1507_ = crate::leanh::lean_box(0);
                            v_isShared_1508_ = v_isSharedCheck_1525_;
                            state = 25;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref_known(v___x_1320_, 3);
                        crate::leanh::lean_dec_ref(v_fn_1306_);
                        crate::leanh::lean_dec(v_offset_1305_);
                        crate::leanh::lean_dec_ref(v_e_1304_);
                        v___x_1526_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32);
                        v___x_1527_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36);
                        v___x_10529__overap_1528_ = l_panic___redArg(v___x_1526_, v___x_1527_);
                        v___x_1529_ = crate::leanh::lean_box((v_a_1308_) as usize);
                        v___x_1530_ = crate::leanh::lean_apply_3(
                            v___x_10529__overap_1528_,
                            v_a_1307_,
                            v___x_1529_,
                            v_a_1309_,
                        );
                        return v___x_1530_;
                    }
                }
            }
            1 => {
                v_fst_1334_ = crate::leanh::lean_ctor_get(v_fst_1329_, 0);
                v_snd_1335_ = crate::leanh::lean_ctor_get(v_fst_1329_, 1);
                v_isSharedCheck_1352_ = (!crate::leanh::lean_is_exclusive(v_fst_1329_)) as u8;
                if v_isSharedCheck_1352_ == 0 {
                    v___x_1337_ = v_fst_1329_;
                    v_isShared_1338_ = v_isSharedCheck_1352_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1335_);
                    crate::leanh::lean_inc(v_fst_1334_);
                    crate::leanh::lean_dec(v_fst_1329_);
                    v___x_1337_ = crate::leanh::lean_box(0);
                    v_isShared_1338_ = v_isSharedCheck_1352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1350_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fn_1321_,
                        v_fst_1326_,
                    );
                if v___x_1350_ == 0 {
                    v___y_1340_ = v___x_1350_;
                    state = 3;
                    continue;
                } else {
                    v___x_1351_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_1322_,
                            v_fst_1334_,
                        );
                    v___y_1340_ = v___x_1351_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_1340_ == 0 {
                    crate::leanh::lean_del_object(v___x_1337_);
                    crate::leanh::lean_del_object(v___x_1332_);
                    crate::leanh::lean_dec_ref_known(v_e_1304_, 2);
                    v___x_10643__overap_1341_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_fst_1326_,
                        v_fst_1334_,
                    );
                    v___x_1342_ = crate::leanh::lean_box((v_a_1308_) as usize);
                    v___x_1343_ = crate::leanh::lean_apply_3(
                        v___x_10643__overap_1341_,
                        v_snd_1335_,
                        v___x_1342_,
                        v_snd_1330_,
                    );
                    return v___x_1343_;
                } else {
                    crate::leanh::lean_dec(v_fst_1334_);
                    crate::leanh::lean_dec(v_fst_1326_);
                    crate::leanh::lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1338_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1337_, 0, v_e_1304_);
                        v___x_1345_ = v___x_1337_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1349_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_e_1304_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_snd_1335_);
                        v___x_1345_ = v_reuseFailAlloc_1349_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1333_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1332_, 0, v___x_1345_);
                    v___x_1347_ = v___x_1332_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1348_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_snd_1330_);
                    v___x_1347_ = v_reuseFailAlloc_1348_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1347_;
            }
            6 => {
                v_fst_1371_ = crate::leanh::lean_ctor_get(v_fst_1366_, 0);
                v_snd_1372_ = crate::leanh::lean_ctor_get(v_fst_1366_, 1);
                v_isSharedCheck_1389_ = (!crate::leanh::lean_is_exclusive(v_fst_1366_)) as u8;
                if v_isSharedCheck_1389_ == 0 {
                    v___x_1374_ = v_fst_1366_;
                    v_isShared_1375_ = v_isSharedCheck_1389_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1372_);
                    crate::leanh::lean_inc(v_fst_1371_);
                    crate::leanh::lean_dec(v_fst_1366_);
                    v___x_1374_ = crate::leanh::lean_box(0);
                    v_isShared_1375_ = v_isSharedCheck_1389_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1387_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_1355_,
                        v_fst_1361_,
                    );
                if v___x_1387_ == 0 {
                    v___y_1377_ = v___x_1387_;
                    state = 8;
                    continue;
                } else {
                    v___x_1388_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1356_,
                            v_fst_1371_,
                        );
                    v___y_1377_ = v___x_1388_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_1377_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1354_);
                    crate::leanh::lean_del_object(v___x_1374_);
                    crate::leanh::lean_del_object(v___x_1369_);
                    crate::leanh::lean_dec_ref_known(v_e_1304_, 3);
                    v___x_10804__overap_1378_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_binderName_1354_,
                        v_binderInfo_1357_,
                        v_fst_1361_,
                        v_fst_1371_,
                    );
                    v___x_1379_ = crate::leanh::lean_box((v_a_1308_) as usize);
                    v___x_1380_ = crate::leanh::lean_apply_3(
                        v___x_10804__overap_1378_,
                        v_snd_1372_,
                        v___x_1379_,
                        v_snd_1367_,
                    );
                    return v___x_1380_;
                } else {
                    crate::leanh::lean_dec(v_fst_1371_);
                    crate::leanh::lean_dec(v_fst_1361_);
                    crate::leanh::lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1375_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1374_, 0, v_e_1304_);
                        v___x_1382_ = v___x_1374_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1386_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_e_1304_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_snd_1372_);
                        v___x_1382_ = v_reuseFailAlloc_1386_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1369_, 0, v___x_1382_);
                    v___x_1384_ = v___x_1369_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1385_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_snd_1367_);
                    v___x_1384_ = v_reuseFailAlloc_1385_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1384_;
            }
            11 => {
                v_fst_1408_ = crate::leanh::lean_ctor_get(v_fst_1403_, 0);
                v_snd_1409_ = crate::leanh::lean_ctor_get(v_fst_1403_, 1);
                v_isSharedCheck_1426_ = (!crate::leanh::lean_is_exclusive(v_fst_1403_)) as u8;
                if v_isSharedCheck_1426_ == 0 {
                    v___x_1411_ = v_fst_1403_;
                    v_isShared_1412_ = v_isSharedCheck_1426_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1409_);
                    crate::leanh::lean_inc(v_fst_1408_);
                    crate::leanh::lean_dec(v_fst_1403_);
                    v___x_1411_ = crate::leanh::lean_box(0);
                    v_isShared_1412_ = v_isSharedCheck_1426_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1424_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_1392_,
                        v_fst_1398_,
                    );
                if v___x_1424_ == 0 {
                    v___y_1414_ = v___x_1424_;
                    state = 13;
                    continue;
                } else {
                    v___x_1425_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1393_,
                            v_fst_1408_,
                        );
                    v___y_1414_ = v___x_1425_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_1414_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1391_);
                    crate::leanh::lean_del_object(v___x_1411_);
                    crate::leanh::lean_del_object(v___x_1406_);
                    crate::leanh::lean_dec_ref_known(v_e_1304_, 3);
                    v___x_10969__overap_1415_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_binderName_1391_,
                        v_binderInfo_1394_,
                        v_fst_1398_,
                        v_fst_1408_,
                    );
                    v___x_1416_ = crate::leanh::lean_box((v_a_1308_) as usize);
                    v___x_1417_ = crate::leanh::lean_apply_3(
                        v___x_10969__overap_1415_,
                        v_snd_1409_,
                        v___x_1416_,
                        v_snd_1404_,
                    );
                    return v___x_1417_;
                } else {
                    crate::leanh::lean_dec(v_fst_1408_);
                    crate::leanh::lean_dec(v_fst_1398_);
                    crate::leanh::lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1412_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1411_, 0, v_e_1304_);
                        v___x_1419_ = v___x_1411_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1423_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_e_1304_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_snd_1409_);
                        v___x_1419_ = v_reuseFailAlloc_1423_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_1407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1406_, 0, v___x_1419_);
                    v___x_1421_ = v___x_1406_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_snd_1404_);
                    v___x_1421_ = v_reuseFailAlloc_1422_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1421_;
            }
            16 => {
                v_fst_1451_ = crate::leanh::lean_ctor_get(v_fst_1446_, 0);
                v_snd_1452_ = crate::leanh::lean_ctor_get(v_fst_1446_, 1);
                v_isSharedCheck_1473_ = (!crate::leanh::lean_is_exclusive(v_fst_1446_)) as u8;
                if v_isSharedCheck_1473_ == 0 {
                    v___x_1454_ = v_fst_1446_;
                    v_isShared_1455_ = v_isSharedCheck_1473_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1452_);
                    crate::leanh::lean_inc(v_fst_1451_);
                    crate::leanh::lean_dec(v_fst_1446_);
                    v___x_1454_ = crate::leanh::lean_box(0);
                    v_isShared_1455_ = v_isSharedCheck_1473_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1471_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_1429_,
                        v_fst_1436_,
                    );
                if v___x_1471_ == 0 {
                    v___y_1457_ = v___x_1471_;
                    state = 18;
                    continue;
                } else {
                    v___x_1472_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_value_1430_,
                            v_fst_1441_,
                        );
                    v___y_1457_ = v___x_1472_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_1457_ == 0 {
                    crate::leanh::lean_inc(v_declName_1428_);
                    crate::leanh::lean_del_object(v___x_1454_);
                    crate::leanh::lean_del_object(v___x_1449_);
                    crate::leanh::lean_dec_ref_known(v_e_1304_, 4);
                    v___x_11156__overap_1458_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_declName_1428_,
                        v_fst_1436_,
                        v_fst_1441_,
                        v_fst_1451_,
                        v_nondep_1432_,
                    );
                    v___x_1459_ = crate::leanh::lean_box((v_a_1308_) as usize);
                    v___x_1460_ = crate::leanh::lean_apply_3(
                        v___x_11156__overap_1458_,
                        v_snd_1452_,
                        v___x_1459_,
                        v_snd_1447_,
                    );
                    return v___x_1460_;
                } else {
                    v___x_1461_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1431_,
                            v_fst_1451_,
                        );
                    if v___x_1461_ == 0 {
                        crate::leanh::lean_inc(v_declName_1428_);
                        crate::leanh::lean_del_object(v___x_1454_);
                        crate::leanh::lean_del_object(v___x_1449_);
                        crate::leanh::lean_dec_ref_known(v_e_1304_, 4);
                        v___x_11158__overap_1462_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
                            v___x_1320_,
                            v___x_1311_,
                            v_declName_1428_,
                            v_fst_1436_,
                            v_fst_1441_,
                            v_fst_1451_,
                            v_nondep_1432_,
                        );
                        v___x_1463_ = crate::leanh::lean_box((v_a_1308_) as usize);
                        v___x_1464_ = crate::leanh::lean_apply_3(
                            v___x_11158__overap_1462_,
                            v_snd_1452_,
                            v___x_1463_,
                            v_snd_1447_,
                        );
                        return v___x_1464_;
                    } else {
                        crate::leanh::lean_dec(v_fst_1451_);
                        crate::leanh::lean_dec(v_fst_1441_);
                        crate::leanh::lean_dec(v_fst_1436_);
                        crate::leanh::lean_dec_ref_known(v___x_1320_, 3);
                        if v_isShared_1455_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1454_, 0, v_e_1304_);
                            v___x_1466_ = v___x_1454_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1470_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_e_1304_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_snd_1452_);
                            v___x_1466_ = v_reuseFailAlloc_1470_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_1450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1449_, 0, v___x_1466_);
                    v___x_1468_ = v___x_1449_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1469_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_snd_1447_);
                    v___x_1468_ = v_reuseFailAlloc_1469_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1468_;
            }
            21 => {
                v_fst_1483_ = crate::leanh::lean_ctor_get(v_fst_1478_, 0);
                v_snd_1484_ = crate::leanh::lean_ctor_get(v_fst_1478_, 1);
                v_isSharedCheck_1498_ = (!crate::leanh::lean_is_exclusive(v_fst_1478_)) as u8;
                if v_isSharedCheck_1498_ == 0 {
                    v___x_1486_ = v_fst_1478_;
                    v_isShared_1487_ = v_isSharedCheck_1498_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1484_);
                    crate::leanh::lean_inc(v_fst_1483_);
                    crate::leanh::lean_dec(v_fst_1478_);
                    v___x_1486_ = crate::leanh::lean_box(0);
                    v_isShared_1487_ = v_isSharedCheck_1498_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1488_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_expr_1476_,
                        v_fst_1483_,
                    );
                if v___x_1488_ == 0 {
                    crate::leanh::lean_inc(v_data_1475_);
                    crate::leanh::lean_del_object(v___x_1486_);
                    crate::leanh::lean_del_object(v___x_1481_);
                    crate::leanh::lean_dec_ref_known(v_e_1304_, 2);
                    v___x_11315__overap_1489_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_data_1475_,
                        v_fst_1483_,
                    );
                    v___x_1490_ = crate::leanh::lean_box((v_a_1308_) as usize);
                    v___x_1491_ = crate::leanh::lean_apply_3(
                        v___x_11315__overap_1489_,
                        v_snd_1484_,
                        v___x_1490_,
                        v_snd_1479_,
                    );
                    return v___x_1491_;
                } else {
                    crate::leanh::lean_dec(v_fst_1483_);
                    crate::leanh::lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1487_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1486_, 0, v_e_1304_);
                        v___x_1493_ = v___x_1486_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1497_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_e_1304_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_snd_1484_);
                        v___x_1493_ = v_reuseFailAlloc_1497_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1482_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1481_, 0, v___x_1493_);
                    v___x_1495_ = v___x_1481_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1496_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_snd_1479_);
                    v___x_1495_ = v_reuseFailAlloc_1496_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1495_;
            }
            25 => {
                v_fst_1509_ = crate::leanh::lean_ctor_get(v_fst_1504_, 0);
                v_snd_1510_ = crate::leanh::lean_ctor_get(v_fst_1504_, 1);
                v_isSharedCheck_1524_ = (!crate::leanh::lean_is_exclusive(v_fst_1504_)) as u8;
                if v_isSharedCheck_1524_ == 0 {
                    v___x_1512_ = v_fst_1504_;
                    v_isShared_1513_ = v_isSharedCheck_1524_;
                    state = 26;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1510_);
                    crate::leanh::lean_inc(v_fst_1509_);
                    crate::leanh::lean_dec(v_fst_1504_);
                    v___x_1512_ = crate::leanh::lean_box(0);
                    v_isShared_1513_ = v_isSharedCheck_1524_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_1514_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_struct_1502_,
                        v_fst_1509_,
                    );
                if v___x_1514_ == 0 {
                    crate::leanh::lean_inc(v_idx_1501_);
                    crate::leanh::lean_inc(v_typeName_1500_);
                    crate::leanh::lean_del_object(v___x_1512_);
                    crate::leanh::lean_del_object(v___x_1507_);
                    crate::leanh::lean_dec_ref_known(v_e_1304_, 3);
                    v___x_11427__overap_1515_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_typeName_1500_,
                        v_idx_1501_,
                        v_fst_1509_,
                    );
                    v___x_1516_ = crate::leanh::lean_box((v_a_1308_) as usize);
                    v___x_1517_ = crate::leanh::lean_apply_3(
                        v___x_11427__overap_1515_,
                        v_snd_1510_,
                        v___x_1516_,
                        v_snd_1505_,
                    );
                    return v___x_1517_;
                } else {
                    crate::leanh::lean_dec(v_fst_1509_);
                    crate::leanh::lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1513_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1512_, 0, v_e_1304_);
                        v___x_1519_ = v___x_1512_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_1523_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_e_1304_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_snd_1510_);
                        v___x_1519_ = v_reuseFailAlloc_1523_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_1508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1519_);
                    v___x_1521_ = v___x_1507_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1522_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_snd_1505_);
                    v___x_1521_ = v_reuseFailAlloc_1522_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
    mut v_e_1531_: *mut crate::leanh::LeanObject,
    mut v_offset_1532_: *mut crate::leanh::LeanObject,
    mut v_f_1533_: *mut crate::leanh::LeanObject,
    mut v_a_1534_: *mut crate::leanh::LeanObject,
    mut v_a_1535_: u8,
    mut v_a_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1537_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3;
    crate::leanh::lean_inc(v_offset_1532_);
    crate::leanh::lean_inc_ref(v_e_1531_);
    v_key_1538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_key_1538_, 0, v_e_1531_);
    crate::leanh::lean_ctor_set(v_key_1538_, 1, v_offset_1532_);
    v___f_1539_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5,
    );
    crate::leanh::lean_inc_ref(v_key_1538_);
    v___x_1540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_1539_,
        v___f_1537_,
        v_a_1534_,
        v_key_1538_,
    );
    if crate::leanh::lean_obj_tag(v___x_1540_) == 1 {
        let mut v_val_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_key_1538_, 2);
        crate::leanh::lean_dec_ref(v_f_1533_);
        crate::leanh::lean_dec(v_offset_1532_);
        crate::leanh::lean_dec_ref(v_e_1531_);
        v_val_1541_ = crate::leanh::lean_ctor_get(v___x_1540_, 0);
        crate::leanh::lean_inc(v_val_1541_);
        crate::leanh::lean_dec_ref_known(v___x_1540_, 1);
        v___x_1542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1542_, 0, v_val_1541_);
        crate::leanh::lean_ctor_set(v___x_1542_, 1, v_a_1534_);
        v___x_1543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1543_, 0, v___x_1542_);
        crate::leanh::lean_ctor_set(v___x_1543_, 1, v_a_1536_);
        return v___x_1543_;
    } else {
        let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1540_);
        v___x_1544_ = crate::leanh::lean_box((v_a_1535_) as usize);
        crate::leanh::lean_inc_ref(v_f_1533_);
        crate::leanh::lean_inc(v_offset_1532_);
        crate::leanh::lean_inc_ref(v_e_1531_);
        v___x_1545_ = crate::leanh::lean_apply_4(
            v_f_1533_,
            v_e_1531_,
            v_offset_1532_,
            v___x_1544_,
            v_a_1536_,
        );
        v_fst_1546_ = crate::leanh::lean_ctor_get(v___x_1545_, 0);
        crate::leanh::lean_inc(v_fst_1546_);
        if crate::leanh::lean_obj_tag(v_fst_1546_) == 1 {
            let mut v_snd_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_f_1533_);
            crate::leanh::lean_dec(v_offset_1532_);
            crate::leanh::lean_dec_ref(v_e_1531_);
            v_snd_1547_ = crate::leanh::lean_ctor_get(v___x_1545_, 1);
            crate::leanh::lean_inc(v_snd_1547_);
            crate::leanh::lean_dec_ref(v___x_1545_);
            v_val_1548_ = crate::leanh::lean_ctor_get(v_fst_1546_, 0);
            crate::leanh::lean_inc(v_val_1548_);
            crate::leanh::lean_dec_ref_known(v_fst_1546_, 1);
            v___x_1549_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                v_key_1538_,
                v_val_1548_,
                v_a_1534_,
                v_snd_1547_,
            );
            return v___x_1549_;
        } else {
            crate::leanh::lean_dec(v_fst_1546_);
            match crate::leanh::lean_obj_tag(v_e_1531_) {
                9 => {
                    let mut v_snd_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_f_1533_);
                    crate::leanh::lean_dec(v_offset_1532_);
                    v_snd_1550_ = crate::leanh::lean_ctor_get(v___x_1545_, 1);
                    crate::leanh::lean_inc(v_snd_1550_);
                    crate::leanh::lean_dec_ref(v___x_1545_);
                    v___x_1551_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1550_,
                    );
                    return v___x_1551_;
                }
                2 => {
                    let mut v_snd_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_f_1533_);
                    crate::leanh::lean_dec(v_offset_1532_);
                    v_snd_1552_ = crate::leanh::lean_ctor_get(v___x_1545_, 1);
                    crate::leanh::lean_inc(v_snd_1552_);
                    crate::leanh::lean_dec_ref(v___x_1545_);
                    v___x_1553_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1552_,
                    );
                    return v___x_1553_;
                }
                0 => {
                    let mut v_snd_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_f_1533_);
                    crate::leanh::lean_dec(v_offset_1532_);
                    v_snd_1554_ = crate::leanh::lean_ctor_get(v___x_1545_, 1);
                    crate::leanh::lean_inc(v_snd_1554_);
                    crate::leanh::lean_dec_ref(v___x_1545_);
                    v___x_1555_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1554_,
                    );
                    return v___x_1555_;
                }
                1 => {
                    let mut v_snd_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_f_1533_);
                    crate::leanh::lean_dec(v_offset_1532_);
                    v_snd_1556_ = crate::leanh::lean_ctor_get(v___x_1545_, 1);
                    crate::leanh::lean_inc(v_snd_1556_);
                    crate::leanh::lean_dec_ref(v___x_1545_);
                    v___x_1557_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1556_,
                    );
                    return v___x_1557_;
                }
                4 => {
                    let mut v_snd_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_f_1533_);
                    crate::leanh::lean_dec(v_offset_1532_);
                    v_snd_1558_ = crate::leanh::lean_ctor_get(v___x_1545_, 1);
                    crate::leanh::lean_inc(v_snd_1558_);
                    crate::leanh::lean_dec_ref(v___x_1545_);
                    v___x_1559_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1558_,
                    );
                    return v___x_1559_;
                }
                3 => {
                    let mut v_snd_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_f_1533_);
                    crate::leanh::lean_dec(v_offset_1532_);
                    v_snd_1560_ = crate::leanh::lean_ctor_get(v___x_1545_, 1);
                    crate::leanh::lean_inc(v_snd_1560_);
                    crate::leanh::lean_dec_ref(v___x_1545_);
                    v___x_1561_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1560_,
                    );
                    return v___x_1561_;
                }
                _ => {
                    let mut v_snd_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_fst_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_snd_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_fst_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_snd_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_snd_1562_ = crate::leanh::lean_ctor_get(v___x_1545_, 1);
                    crate::leanh::lean_inc(v_snd_1562_);
                    crate::leanh::lean_dec_ref(v___x_1545_);
                    v___x_1563_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(
                        v_e_1531_,
                        v_offset_1532_,
                        v_f_1533_,
                        v_a_1534_,
                        v_a_1535_,
                        v_snd_1562_,
                    );
                    v_fst_1564_ = crate::leanh::lean_ctor_get(v___x_1563_, 0);
                    crate::leanh::lean_inc(v_fst_1564_);
                    v_snd_1565_ = crate::leanh::lean_ctor_get(v___x_1563_, 1);
                    crate::leanh::lean_inc(v_snd_1565_);
                    crate::leanh::lean_dec_ref(v___x_1563_);
                    v_fst_1566_ = crate::leanh::lean_ctor_get(v_fst_1564_, 0);
                    crate::leanh::lean_inc(v_fst_1566_);
                    v_snd_1567_ = crate::leanh::lean_ctor_get(v_fst_1564_, 1);
                    crate::leanh::lean_inc(v_snd_1567_);
                    crate::leanh::lean_dec(v_fst_1564_);
                    v___x_1568_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_fst_1566_,
                        v_snd_1567_,
                        v_snd_1565_,
                    );
                    return v___x_1568_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(
    mut v_e_1569_: *mut crate::leanh::LeanObject,
    mut v_offset_1570_: *mut crate::leanh::LeanObject,
    mut v_f_1571_: *mut crate::leanh::LeanObject,
    mut v_a_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
    mut v_a_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1575_: u8 = 0;
    let mut v_res_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1575_ = (crate::leanh::lean_unbox(v_a_1573_) as u8);
    v_res_1576_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
        v_e_1569_,
        v_offset_1570_,
        v_f_1571_,
        v_a_1572_,
        v_a_boxed_1575_,
        v_a_1574_,
    );
    return v_res_1576_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(
    mut v_e_1577_: *mut crate::leanh::LeanObject,
    mut v_offset_1578_: *mut crate::leanh::LeanObject,
    mut v_fn_1579_: *mut crate::leanh::LeanObject,
    mut v_a_1580_: *mut crate::leanh::LeanObject,
    mut v_a_1581_: *mut crate::leanh::LeanObject,
    mut v_a_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1583_: u8 = 0;
    let mut v_res_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1583_ = (crate::leanh::lean_unbox(v_a_1581_) as u8);
    v_res_1584_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(
        v_e_1577_,
        v_offset_1578_,
        v_fn_1579_,
        v_a_1580_,
        v_a_boxed_1583_,
        v_a_1582_,
    );
    return v_res_1584_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter___redArg(
    mut v_____do__lift_1585_: *mut crate::leanh::LeanObject,
    mut v_h__1_1586_: *mut crate::leanh::LeanObject,
    mut v_h__2_1587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1585_) == 1 {
        let mut v_val_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1587_);
        v_val_1588_ = crate::leanh::lean_ctor_get(v_____do__lift_1585_, 0);
        crate::leanh::lean_inc(v_val_1588_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1585_, 1);
        v___x_1589_ = crate::leanh::lean_apply_1(v_h__1_1586_, v_val_1588_);
        return v___x_1589_;
    } else {
        let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1586_);
        v___x_1590_ = crate::leanh::lean_apply_2(
            v_h__2_1587_,
            v_____do__lift_1585_,
            crate::leanh::lean_box(0),
        );
        return v___x_1590_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(
    mut v_motive_1591_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1592_: *mut crate::leanh::LeanObject,
    mut v_h__1_1593_: *mut crate::leanh::LeanObject,
    mut v_h__2_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1592_) == 1 {
        let mut v_val_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1594_);
        v_val_1595_ = crate::leanh::lean_ctor_get(v_____do__lift_1592_, 0);
        crate::leanh::lean_inc(v_val_1595_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1592_, 1);
        v___x_1596_ = crate::leanh::lean_apply_1(v_h__1_1593_, v_val_1595_);
        return v___x_1596_;
    } else {
        let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1593_);
        v___x_1597_ = crate::leanh::lean_apply_2(
            v_h__2_1594_,
            v_____do__lift_1592_,
            crate::leanh::lean_box(0),
        );
        return v___x_1597_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(
    mut v_e_1598_: *mut crate::leanh::LeanObject,
    mut v_h__1_1599_: *mut crate::leanh::LeanObject,
    mut v_h__2_1600_: *mut crate::leanh::LeanObject,
    mut v_h__3_1601_: *mut crate::leanh::LeanObject,
    mut v_h__4_1602_: *mut crate::leanh::LeanObject,
    mut v_h__5_1603_: *mut crate::leanh::LeanObject,
    mut v_h__6_1604_: *mut crate::leanh::LeanObject,
    mut v_h__7_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_e_1598_) {
        9 => {
            let mut v_a_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1605_);
            crate::leanh::lean_dec(v_h__6_1604_);
            crate::leanh::lean_dec(v_h__5_1603_);
            crate::leanh::lean_dec(v_h__4_1602_);
            crate::leanh::lean_dec(v_h__3_1601_);
            crate::leanh::lean_dec(v_h__2_1600_);
            v_a_1606_ = crate::leanh::lean_ctor_get(v_e_1598_, 0);
            crate::leanh::lean_inc_ref(v_a_1606_);
            crate::leanh::lean_dec_ref_known(v_e_1598_, 1);
            v___x_1607_ = crate::leanh::lean_apply_1(v_h__1_1599_, v_a_1606_);
            return v___x_1607_;
        }
        2 => {
            let mut v_mvarId_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1605_);
            crate::leanh::lean_dec(v_h__6_1604_);
            crate::leanh::lean_dec(v_h__5_1603_);
            crate::leanh::lean_dec(v_h__4_1602_);
            crate::leanh::lean_dec(v_h__3_1601_);
            crate::leanh::lean_dec(v_h__1_1599_);
            v_mvarId_1608_ = crate::leanh::lean_ctor_get(v_e_1598_, 0);
            crate::leanh::lean_inc(v_mvarId_1608_);
            crate::leanh::lean_dec_ref_known(v_e_1598_, 1);
            v___x_1609_ = crate::leanh::lean_apply_1(v_h__2_1600_, v_mvarId_1608_);
            return v___x_1609_;
        }
        0 => {
            let mut v_deBruijnIndex_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1605_);
            crate::leanh::lean_dec(v_h__6_1604_);
            crate::leanh::lean_dec(v_h__5_1603_);
            crate::leanh::lean_dec(v_h__4_1602_);
            crate::leanh::lean_dec(v_h__2_1600_);
            crate::leanh::lean_dec(v_h__1_1599_);
            v_deBruijnIndex_1610_ = crate::leanh::lean_ctor_get(v_e_1598_, 0);
            crate::leanh::lean_inc(v_deBruijnIndex_1610_);
            crate::leanh::lean_dec_ref_known(v_e_1598_, 1);
            v___x_1611_ = crate::leanh::lean_apply_1(v_h__3_1601_, v_deBruijnIndex_1610_);
            return v___x_1611_;
        }
        1 => {
            let mut v_fvarId_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1605_);
            crate::leanh::lean_dec(v_h__6_1604_);
            crate::leanh::lean_dec(v_h__5_1603_);
            crate::leanh::lean_dec(v_h__3_1601_);
            crate::leanh::lean_dec(v_h__2_1600_);
            crate::leanh::lean_dec(v_h__1_1599_);
            v_fvarId_1612_ = crate::leanh::lean_ctor_get(v_e_1598_, 0);
            crate::leanh::lean_inc(v_fvarId_1612_);
            crate::leanh::lean_dec_ref_known(v_e_1598_, 1);
            v___x_1613_ = crate::leanh::lean_apply_1(v_h__4_1602_, v_fvarId_1612_);
            return v___x_1613_;
        }
        4 => {
            let mut v_declName_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_us_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1605_);
            crate::leanh::lean_dec(v_h__6_1604_);
            crate::leanh::lean_dec(v_h__4_1602_);
            crate::leanh::lean_dec(v_h__3_1601_);
            crate::leanh::lean_dec(v_h__2_1600_);
            crate::leanh::lean_dec(v_h__1_1599_);
            v_declName_1614_ = crate::leanh::lean_ctor_get(v_e_1598_, 0);
            crate::leanh::lean_inc(v_declName_1614_);
            v_us_1615_ = crate::leanh::lean_ctor_get(v_e_1598_, 1);
            crate::leanh::lean_inc(v_us_1615_);
            crate::leanh::lean_dec_ref_known(v_e_1598_, 2);
            v___x_1616_ = crate::leanh::lean_apply_2(v_h__5_1603_, v_declName_1614_, v_us_1615_);
            return v___x_1616_;
        }
        3 => {
            let mut v_u_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1605_);
            crate::leanh::lean_dec(v_h__5_1603_);
            crate::leanh::lean_dec(v_h__4_1602_);
            crate::leanh::lean_dec(v_h__3_1601_);
            crate::leanh::lean_dec(v_h__2_1600_);
            crate::leanh::lean_dec(v_h__1_1599_);
            v_u_1617_ = crate::leanh::lean_ctor_get(v_e_1598_, 0);
            crate::leanh::lean_inc(v_u_1617_);
            crate::leanh::lean_dec_ref_known(v_e_1598_, 1);
            v___x_1618_ = crate::leanh::lean_apply_1(v_h__6_1604_, v_u_1617_);
            return v___x_1618_;
        }
        _ => {
            let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_1604_);
            crate::leanh::lean_dec(v_h__5_1603_);
            crate::leanh::lean_dec(v_h__4_1602_);
            crate::leanh::lean_dec(v_h__3_1601_);
            crate::leanh::lean_dec(v_h__2_1600_);
            crate::leanh::lean_dec(v_h__1_1599_);
            v___x_1619_ = crate::leanh::lean_apply_7(
                v_h__7_1605_,
                v_e_1598_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1619_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(
    mut v_motive_1620_: *mut crate::leanh::LeanObject,
    mut v_e_1621_: *mut crate::leanh::LeanObject,
    mut v_h__1_1622_: *mut crate::leanh::LeanObject,
    mut v_h__2_1623_: *mut crate::leanh::LeanObject,
    mut v_h__3_1624_: *mut crate::leanh::LeanObject,
    mut v_h__4_1625_: *mut crate::leanh::LeanObject,
    mut v_h__5_1626_: *mut crate::leanh::LeanObject,
    mut v_h__6_1627_: *mut crate::leanh::LeanObject,
    mut v_h__7_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_e_1621_) {
        9 => {
            let mut v_a_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1628_);
            crate::leanh::lean_dec(v_h__6_1627_);
            crate::leanh::lean_dec(v_h__5_1626_);
            crate::leanh::lean_dec(v_h__4_1625_);
            crate::leanh::lean_dec(v_h__3_1624_);
            crate::leanh::lean_dec(v_h__2_1623_);
            v_a_1629_ = crate::leanh::lean_ctor_get(v_e_1621_, 0);
            crate::leanh::lean_inc_ref(v_a_1629_);
            crate::leanh::lean_dec_ref_known(v_e_1621_, 1);
            v___x_1630_ = crate::leanh::lean_apply_1(v_h__1_1622_, v_a_1629_);
            return v___x_1630_;
        }
        2 => {
            let mut v_mvarId_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1628_);
            crate::leanh::lean_dec(v_h__6_1627_);
            crate::leanh::lean_dec(v_h__5_1626_);
            crate::leanh::lean_dec(v_h__4_1625_);
            crate::leanh::lean_dec(v_h__3_1624_);
            crate::leanh::lean_dec(v_h__1_1622_);
            v_mvarId_1631_ = crate::leanh::lean_ctor_get(v_e_1621_, 0);
            crate::leanh::lean_inc(v_mvarId_1631_);
            crate::leanh::lean_dec_ref_known(v_e_1621_, 1);
            v___x_1632_ = crate::leanh::lean_apply_1(v_h__2_1623_, v_mvarId_1631_);
            return v___x_1632_;
        }
        0 => {
            let mut v_deBruijnIndex_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1628_);
            crate::leanh::lean_dec(v_h__6_1627_);
            crate::leanh::lean_dec(v_h__5_1626_);
            crate::leanh::lean_dec(v_h__4_1625_);
            crate::leanh::lean_dec(v_h__2_1623_);
            crate::leanh::lean_dec(v_h__1_1622_);
            v_deBruijnIndex_1633_ = crate::leanh::lean_ctor_get(v_e_1621_, 0);
            crate::leanh::lean_inc(v_deBruijnIndex_1633_);
            crate::leanh::lean_dec_ref_known(v_e_1621_, 1);
            v___x_1634_ = crate::leanh::lean_apply_1(v_h__3_1624_, v_deBruijnIndex_1633_);
            return v___x_1634_;
        }
        1 => {
            let mut v_fvarId_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1628_);
            crate::leanh::lean_dec(v_h__6_1627_);
            crate::leanh::lean_dec(v_h__5_1626_);
            crate::leanh::lean_dec(v_h__3_1624_);
            crate::leanh::lean_dec(v_h__2_1623_);
            crate::leanh::lean_dec(v_h__1_1622_);
            v_fvarId_1635_ = crate::leanh::lean_ctor_get(v_e_1621_, 0);
            crate::leanh::lean_inc(v_fvarId_1635_);
            crate::leanh::lean_dec_ref_known(v_e_1621_, 1);
            v___x_1636_ = crate::leanh::lean_apply_1(v_h__4_1625_, v_fvarId_1635_);
            return v___x_1636_;
        }
        4 => {
            let mut v_declName_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_us_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1628_);
            crate::leanh::lean_dec(v_h__6_1627_);
            crate::leanh::lean_dec(v_h__4_1625_);
            crate::leanh::lean_dec(v_h__3_1624_);
            crate::leanh::lean_dec(v_h__2_1623_);
            crate::leanh::lean_dec(v_h__1_1622_);
            v_declName_1637_ = crate::leanh::lean_ctor_get(v_e_1621_, 0);
            crate::leanh::lean_inc(v_declName_1637_);
            v_us_1638_ = crate::leanh::lean_ctor_get(v_e_1621_, 1);
            crate::leanh::lean_inc(v_us_1638_);
            crate::leanh::lean_dec_ref_known(v_e_1621_, 2);
            v___x_1639_ = crate::leanh::lean_apply_2(v_h__5_1626_, v_declName_1637_, v_us_1638_);
            return v___x_1639_;
        }
        3 => {
            let mut v_u_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_1628_);
            crate::leanh::lean_dec(v_h__5_1626_);
            crate::leanh::lean_dec(v_h__4_1625_);
            crate::leanh::lean_dec(v_h__3_1624_);
            crate::leanh::lean_dec(v_h__2_1623_);
            crate::leanh::lean_dec(v_h__1_1622_);
            v_u_1640_ = crate::leanh::lean_ctor_get(v_e_1621_, 0);
            crate::leanh::lean_inc(v_u_1640_);
            crate::leanh::lean_dec_ref_known(v_e_1621_, 1);
            v___x_1641_ = crate::leanh::lean_apply_1(v_h__6_1627_, v_u_1640_);
            return v___x_1641_;
        }
        _ => {
            let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_1627_);
            crate::leanh::lean_dec(v_h__5_1626_);
            crate::leanh::lean_dec(v_h__4_1625_);
            crate::leanh::lean_dec(v_h__3_1624_);
            crate::leanh::lean_dec(v_h__2_1623_);
            crate::leanh::lean_dec(v_h__1_1622_);
            v___x_1642_ = crate::leanh::lean_apply_7(
                v_h__7_1628_,
                v_e_1621_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1642_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(
    mut v_e_1643_: *mut crate::leanh::LeanObject,
    mut v_h__1_1644_: *mut crate::leanh::LeanObject,
    mut v_h__2_1645_: *mut crate::leanh::LeanObject,
    mut v_h__3_1646_: *mut crate::leanh::LeanObject,
    mut v_h__4_1647_: *mut crate::leanh::LeanObject,
    mut v_h__5_1648_: *mut crate::leanh::LeanObject,
    mut v_h__6_1649_: *mut crate::leanh::LeanObject,
    mut v_h__7_1650_: *mut crate::leanh::LeanObject,
    mut v_h__8_1651_: *mut crate::leanh::LeanObject,
    mut v_h__9_1652_: *mut crate::leanh::LeanObject,
    mut v_h__10_1653_: *mut crate::leanh::LeanObject,
    mut v_h__11_1654_: *mut crate::leanh::LeanObject,
    mut v_h__12_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_e_1643_) {
        0 => {
            let mut v_deBruijnIndex_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_deBruijnIndex_1656_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_deBruijnIndex_1656_);
            crate::leanh::lean_dec_ref_known(v_e_1643_, 1);
            v___x_1657_ = crate::leanh::lean_apply_1(v_h__3_1646_, v_deBruijnIndex_1656_);
            return v___x_1657_;
        }
        1 => {
            let mut v_fvarId_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_fvarId_1658_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_fvarId_1658_);
            crate::leanh::lean_dec_ref_known(v_e_1643_, 1);
            v___x_1659_ = crate::leanh::lean_apply_1(v_h__4_1647_, v_fvarId_1658_);
            return v___x_1659_;
        }
        2 => {
            let mut v_mvarId_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_mvarId_1660_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_mvarId_1660_);
            crate::leanh::lean_dec_ref_known(v_e_1643_, 1);
            v___x_1661_ = crate::leanh::lean_apply_1(v_h__2_1645_, v_mvarId_1660_);
            return v___x_1661_;
        }
        3 => {
            let mut v_u_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_u_1662_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_u_1662_);
            crate::leanh::lean_dec_ref_known(v_e_1643_, 1);
            v___x_1663_ = crate::leanh::lean_apply_1(v_h__6_1649_, v_u_1662_);
            return v___x_1663_;
        }
        4 => {
            let mut v_declName_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_us_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_declName_1664_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_declName_1664_);
            v_us_1665_ = crate::leanh::lean_ctor_get(v_e_1643_, 1);
            crate::leanh::lean_inc(v_us_1665_);
            crate::leanh::lean_dec_ref_known(v_e_1643_, 2);
            v___x_1666_ = crate::leanh::lean_apply_2(v_h__5_1648_, v_declName_1664_, v_us_1665_);
            return v___x_1666_;
        }
        5 => {
            let mut v_fn_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_arg_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_fn_1667_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc_ref(v_fn_1667_);
            v_arg_1668_ = crate::leanh::lean_ctor_get(v_e_1643_, 1);
            crate::leanh::lean_inc_ref(v_arg_1668_);
            crate::leanh::lean_dec_ref_known(v_e_1643_, 2);
            v___x_1669_ = crate::leanh::lean_apply_2(v_h__7_1650_, v_fn_1667_, v_arg_1668_);
            return v___x_1669_;
        }
        6 => {
            let mut v_binderName_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderType_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1673_: u8 = 0;
            let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_binderName_1670_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_binderName_1670_);
            v_binderType_1671_ = crate::leanh::lean_ctor_get(v_e_1643_, 1);
            crate::leanh::lean_inc_ref(v_binderType_1671_);
            v_body_1672_ = crate::leanh::lean_ctor_get(v_e_1643_, 2);
            crate::leanh::lean_inc_ref(v_body_1672_);
            v_binderInfo_1673_ = crate::leanh::lean_ctor_get_uint8(
                v_e_1643_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_e_1643_, 3);
            v___x_1674_ = crate::leanh::lean_box((v_binderInfo_1673_) as usize);
            v___x_1675_ = crate::leanh::lean_apply_4(
                v_h__11_1654_,
                v_binderName_1670_,
                v_binderType_1671_,
                v_body_1672_,
                v___x_1674_,
            );
            return v___x_1675_;
        }
        7 => {
            let mut v_binderName_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderType_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1679_: u8 = 0;
            let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_binderName_1676_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_binderName_1676_);
            v_binderType_1677_ = crate::leanh::lean_ctor_get(v_e_1643_, 1);
            crate::leanh::lean_inc_ref(v_binderType_1677_);
            v_body_1678_ = crate::leanh::lean_ctor_get(v_e_1643_, 2);
            crate::leanh::lean_inc_ref(v_body_1678_);
            v_binderInfo_1679_ = crate::leanh::lean_ctor_get_uint8(
                v_e_1643_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_e_1643_, 3);
            v___x_1680_ = crate::leanh::lean_box((v_binderInfo_1679_) as usize);
            v___x_1681_ = crate::leanh::lean_apply_4(
                v_h__10_1653_,
                v_binderName_1676_,
                v_binderType_1677_,
                v_body_1678_,
                v___x_1680_,
            );
            return v___x_1681_;
        }
        8 => {
            let mut v_declName_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_nondep_1686_: u8 = 0;
            let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_declName_1682_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_declName_1682_);
            v_type_1683_ = crate::leanh::lean_ctor_get(v_e_1643_, 1);
            crate::leanh::lean_inc_ref(v_type_1683_);
            v_value_1684_ = crate::leanh::lean_ctor_get(v_e_1643_, 2);
            crate::leanh::lean_inc_ref(v_value_1684_);
            v_body_1685_ = crate::leanh::lean_ctor_get(v_e_1643_, 3);
            crate::leanh::lean_inc_ref(v_body_1685_);
            v_nondep_1686_ = crate::leanh::lean_ctor_get_uint8(
                v_e_1643_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_e_1643_, 4);
            v___x_1687_ = crate::leanh::lean_box((v_nondep_1686_) as usize);
            v___x_1688_ = crate::leanh::lean_apply_5(
                v_h__12_1655_,
                v_declName_1682_,
                v_type_1683_,
                v_value_1684_,
                v_body_1685_,
                v___x_1687_,
            );
            return v___x_1688_;
        }
        9 => {
            let mut v_a_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            v_a_1689_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc_ref(v_a_1689_);
            crate::leanh::lean_dec_ref_known(v_e_1643_, 1);
            v___x_1690_ = crate::leanh::lean_apply_1(v_h__1_1644_, v_a_1689_);
            return v___x_1690_;
        }
        10 => {
            let mut v_data_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__9_1652_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_data_1691_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_data_1691_);
            v_expr_1692_ = crate::leanh::lean_ctor_get(v_e_1643_, 1);
            crate::leanh::lean_inc_ref(v_expr_1692_);
            crate::leanh::lean_dec_ref_known(v_e_1643_, 2);
            v___x_1693_ = crate::leanh::lean_apply_2(v_h__8_1651_, v_data_1691_, v_expr_1692_);
            return v___x_1693_;
        }
        _ => {
            let mut v_typeName_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_struct_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1655_);
            crate::leanh::lean_dec(v_h__11_1654_);
            crate::leanh::lean_dec(v_h__10_1653_);
            crate::leanh::lean_dec(v_h__8_1651_);
            crate::leanh::lean_dec(v_h__7_1650_);
            crate::leanh::lean_dec(v_h__6_1649_);
            crate::leanh::lean_dec(v_h__5_1648_);
            crate::leanh::lean_dec(v_h__4_1647_);
            crate::leanh::lean_dec(v_h__3_1646_);
            crate::leanh::lean_dec(v_h__2_1645_);
            crate::leanh::lean_dec(v_h__1_1644_);
            v_typeName_1694_ = crate::leanh::lean_ctor_get(v_e_1643_, 0);
            crate::leanh::lean_inc(v_typeName_1694_);
            v_idx_1695_ = crate::leanh::lean_ctor_get(v_e_1643_, 1);
            crate::leanh::lean_inc(v_idx_1695_);
            v_struct_1696_ = crate::leanh::lean_ctor_get(v_e_1643_, 2);
            crate::leanh::lean_inc_ref(v_struct_1696_);
            crate::leanh::lean_dec_ref_known(v_e_1643_, 3);
            v___x_1697_ = crate::leanh::lean_apply_3(
                v_h__9_1652_,
                v_typeName_1694_,
                v_idx_1695_,
                v_struct_1696_,
            );
            return v___x_1697_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(
    mut v_motive_1698_: *mut crate::leanh::LeanObject,
    mut v_e_1699_: *mut crate::leanh::LeanObject,
    mut v_h__1_1700_: *mut crate::leanh::LeanObject,
    mut v_h__2_1701_: *mut crate::leanh::LeanObject,
    mut v_h__3_1702_: *mut crate::leanh::LeanObject,
    mut v_h__4_1703_: *mut crate::leanh::LeanObject,
    mut v_h__5_1704_: *mut crate::leanh::LeanObject,
    mut v_h__6_1705_: *mut crate::leanh::LeanObject,
    mut v_h__7_1706_: *mut crate::leanh::LeanObject,
    mut v_h__8_1707_: *mut crate::leanh::LeanObject,
    mut v_h__9_1708_: *mut crate::leanh::LeanObject,
    mut v_h__10_1709_: *mut crate::leanh::LeanObject,
    mut v_h__11_1710_: *mut crate::leanh::LeanObject,
    mut v_h__12_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_e_1699_) {
        0 => {
            let mut v_deBruijnIndex_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_deBruijnIndex_1712_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_deBruijnIndex_1712_);
            crate::leanh::lean_dec_ref_known(v_e_1699_, 1);
            v___x_1713_ = crate::leanh::lean_apply_1(v_h__3_1702_, v_deBruijnIndex_1712_);
            return v___x_1713_;
        }
        1 => {
            let mut v_fvarId_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_fvarId_1714_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_fvarId_1714_);
            crate::leanh::lean_dec_ref_known(v_e_1699_, 1);
            v___x_1715_ = crate::leanh::lean_apply_1(v_h__4_1703_, v_fvarId_1714_);
            return v___x_1715_;
        }
        2 => {
            let mut v_mvarId_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_mvarId_1716_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_mvarId_1716_);
            crate::leanh::lean_dec_ref_known(v_e_1699_, 1);
            v___x_1717_ = crate::leanh::lean_apply_1(v_h__2_1701_, v_mvarId_1716_);
            return v___x_1717_;
        }
        3 => {
            let mut v_u_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_u_1718_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_u_1718_);
            crate::leanh::lean_dec_ref_known(v_e_1699_, 1);
            v___x_1719_ = crate::leanh::lean_apply_1(v_h__6_1705_, v_u_1718_);
            return v___x_1719_;
        }
        4 => {
            let mut v_declName_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_us_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_declName_1720_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_declName_1720_);
            v_us_1721_ = crate::leanh::lean_ctor_get(v_e_1699_, 1);
            crate::leanh::lean_inc(v_us_1721_);
            crate::leanh::lean_dec_ref_known(v_e_1699_, 2);
            v___x_1722_ = crate::leanh::lean_apply_2(v_h__5_1704_, v_declName_1720_, v_us_1721_);
            return v___x_1722_;
        }
        5 => {
            let mut v_fn_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_arg_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_fn_1723_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc_ref(v_fn_1723_);
            v_arg_1724_ = crate::leanh::lean_ctor_get(v_e_1699_, 1);
            crate::leanh::lean_inc_ref(v_arg_1724_);
            crate::leanh::lean_dec_ref_known(v_e_1699_, 2);
            v___x_1725_ = crate::leanh::lean_apply_2(v_h__7_1706_, v_fn_1723_, v_arg_1724_);
            return v___x_1725_;
        }
        6 => {
            let mut v_binderName_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderType_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1729_: u8 = 0;
            let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_binderName_1726_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_binderName_1726_);
            v_binderType_1727_ = crate::leanh::lean_ctor_get(v_e_1699_, 1);
            crate::leanh::lean_inc_ref(v_binderType_1727_);
            v_body_1728_ = crate::leanh::lean_ctor_get(v_e_1699_, 2);
            crate::leanh::lean_inc_ref(v_body_1728_);
            v_binderInfo_1729_ = crate::leanh::lean_ctor_get_uint8(
                v_e_1699_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_e_1699_, 3);
            v___x_1730_ = crate::leanh::lean_box((v_binderInfo_1729_) as usize);
            v___x_1731_ = crate::leanh::lean_apply_4(
                v_h__11_1710_,
                v_binderName_1726_,
                v_binderType_1727_,
                v_body_1728_,
                v___x_1730_,
            );
            return v___x_1731_;
        }
        7 => {
            let mut v_binderName_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderType_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1735_: u8 = 0;
            let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_binderName_1732_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_binderName_1732_);
            v_binderType_1733_ = crate::leanh::lean_ctor_get(v_e_1699_, 1);
            crate::leanh::lean_inc_ref(v_binderType_1733_);
            v_body_1734_ = crate::leanh::lean_ctor_get(v_e_1699_, 2);
            crate::leanh::lean_inc_ref(v_body_1734_);
            v_binderInfo_1735_ = crate::leanh::lean_ctor_get_uint8(
                v_e_1699_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_e_1699_, 3);
            v___x_1736_ = crate::leanh::lean_box((v_binderInfo_1735_) as usize);
            v___x_1737_ = crate::leanh::lean_apply_4(
                v_h__10_1709_,
                v_binderName_1732_,
                v_binderType_1733_,
                v_body_1734_,
                v___x_1736_,
            );
            return v___x_1737_;
        }
        8 => {
            let mut v_declName_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_nondep_1742_: u8 = 0;
            let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_declName_1738_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_declName_1738_);
            v_type_1739_ = crate::leanh::lean_ctor_get(v_e_1699_, 1);
            crate::leanh::lean_inc_ref(v_type_1739_);
            v_value_1740_ = crate::leanh::lean_ctor_get(v_e_1699_, 2);
            crate::leanh::lean_inc_ref(v_value_1740_);
            v_body_1741_ = crate::leanh::lean_ctor_get(v_e_1699_, 3);
            crate::leanh::lean_inc_ref(v_body_1741_);
            v_nondep_1742_ = crate::leanh::lean_ctor_get_uint8(
                v_e_1699_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_e_1699_, 4);
            v___x_1743_ = crate::leanh::lean_box((v_nondep_1742_) as usize);
            v___x_1744_ = crate::leanh::lean_apply_5(
                v_h__12_1711_,
                v_declName_1738_,
                v_type_1739_,
                v_value_1740_,
                v_body_1741_,
                v___x_1743_,
            );
            return v___x_1744_;
        }
        9 => {
            let mut v_a_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            v_a_1745_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc_ref(v_a_1745_);
            crate::leanh::lean_dec_ref_known(v_e_1699_, 1);
            v___x_1746_ = crate::leanh::lean_apply_1(v_h__1_1700_, v_a_1745_);
            return v___x_1746_;
        }
        10 => {
            let mut v_data_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__9_1708_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_data_1747_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_data_1747_);
            v_expr_1748_ = crate::leanh::lean_ctor_get(v_e_1699_, 1);
            crate::leanh::lean_inc_ref(v_expr_1748_);
            crate::leanh::lean_dec_ref_known(v_e_1699_, 2);
            v___x_1749_ = crate::leanh::lean_apply_2(v_h__8_1707_, v_data_1747_, v_expr_1748_);
            return v___x_1749_;
        }
        _ => {
            let mut v_typeName_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_struct_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__12_1711_);
            crate::leanh::lean_dec(v_h__11_1710_);
            crate::leanh::lean_dec(v_h__10_1709_);
            crate::leanh::lean_dec(v_h__8_1707_);
            crate::leanh::lean_dec(v_h__7_1706_);
            crate::leanh::lean_dec(v_h__6_1705_);
            crate::leanh::lean_dec(v_h__5_1704_);
            crate::leanh::lean_dec(v_h__4_1703_);
            crate::leanh::lean_dec(v_h__3_1702_);
            crate::leanh::lean_dec(v_h__2_1701_);
            crate::leanh::lean_dec(v_h__1_1700_);
            v_typeName_1750_ = crate::leanh::lean_ctor_get(v_e_1699_, 0);
            crate::leanh::lean_inc(v_typeName_1750_);
            v_idx_1751_ = crate::leanh::lean_ctor_get(v_e_1699_, 1);
            crate::leanh::lean_inc(v_idx_1751_);
            v_struct_1752_ = crate::leanh::lean_ctor_get(v_e_1699_, 2);
            crate::leanh::lean_inc_ref(v_struct_1752_);
            crate::leanh::lean_dec_ref_known(v_e_1699_, 3);
            v___x_1753_ = crate::leanh::lean_apply_3(
                v_h__9_1708_,
                v_typeName_1750_,
                v_idx_1751_,
                v_struct_1752_,
            );
            return v___x_1753_;
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Sym_replaceS_x27___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = crate::leanh::lean_box(0);
    v___x_1755_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1756_ = lean_mk_array(v___x_1755_, v___x_1754_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_replaceS_x27___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS_x27___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS_x27___closed__0_once),
        _init_l_Lean_Meta_Sym_replaceS_x27___closed__0,
    );
    v___x_1758_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1759_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1759_, 0, v___x_1758_);
    crate::leanh::lean_ctor_set(v___x_1759_, 1, v___x_1757_);
    return v___x_1759_;
}
pub unsafe fn l_Lean_Meta_Sym_replaceS_x27(
    mut v_e_1760_: *mut crate::leanh::LeanObject,
    mut v_f_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: u8,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1771_: u8 = 0;
    let mut v_val_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_unused_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1781_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut v_unused_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut v_unused_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v_unused_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1808_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_unused_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v_unused_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v_unused_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_unused_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1764_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1765_ = crate::leanh::lean_box((v_a_1762_) as usize);
                crate::leanh::lean_inc_ref(v_f_1761_);
                crate::leanh::lean_inc_ref(v_e_1760_);
                v___x_1766_ = crate::leanh::lean_apply_4(
                    v_f_1761_,
                    v_e_1760_,
                    v___x_1764_,
                    v___x_1765_,
                    v_a_1763_,
                );
                v_fst_1767_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                crate::leanh::lean_inc(v_fst_1767_);
                if crate::leanh::lean_obj_tag(v_fst_1767_) == 1 {
                    crate::leanh::lean_dec_ref(v_f_1761_);
                    crate::leanh::lean_dec_ref(v_e_1760_);
                    v_snd_1768_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                    v_isSharedCheck_1776_ = (!crate::leanh::lean_is_exclusive(v___x_1766_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v_unused_1777_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                        crate::leanh::lean_dec(v_unused_1777_);
                        v___x_1770_ = v___x_1766_;
                        v_isShared_1771_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1768_);
                        crate::leanh::lean_dec(v___x_1766_);
                        v___x_1770_ = crate::leanh::lean_box(0);
                        v_isShared_1771_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1767_);
                    match crate::leanh::lean_obj_tag(v_e_1760_) {
                        9 => {
                            crate::leanh::lean_dec_ref(v_f_1761_);
                            v_snd_1778_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1785_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1785_ == 0 {
                                v_unused_1786_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                                crate::leanh::lean_dec(v_unused_1786_);
                                v___x_1780_ = v___x_1766_;
                                v_isShared_1781_ = v_isSharedCheck_1785_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1778_);
                                crate::leanh::lean_dec(v___x_1766_);
                                v___x_1780_ = crate::leanh::lean_box(0);
                                v_isShared_1781_ = v_isSharedCheck_1785_;
                                state = 3;
                                continue;
                            }
                        }
                        2 => {
                            crate::leanh::lean_dec_ref(v_f_1761_);
                            v_snd_1787_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1794_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1794_ == 0 {
                                v_unused_1795_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                                crate::leanh::lean_dec(v_unused_1795_);
                                v___x_1789_ = v___x_1766_;
                                v_isShared_1790_ = v_isSharedCheck_1794_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1787_);
                                crate::leanh::lean_dec(v___x_1766_);
                                v___x_1789_ = crate::leanh::lean_box(0);
                                v_isShared_1790_ = v_isSharedCheck_1794_;
                                state = 5;
                                continue;
                            }
                        }
                        0 => {
                            crate::leanh::lean_dec_ref(v_f_1761_);
                            v_snd_1796_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1803_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1803_ == 0 {
                                v_unused_1804_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                                crate::leanh::lean_dec(v_unused_1804_);
                                v___x_1798_ = v___x_1766_;
                                v_isShared_1799_ = v_isSharedCheck_1803_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1796_);
                                crate::leanh::lean_dec(v___x_1766_);
                                v___x_1798_ = crate::leanh::lean_box(0);
                                v_isShared_1799_ = v_isSharedCheck_1803_;
                                state = 7;
                                continue;
                            }
                        }
                        1 => {
                            crate::leanh::lean_dec_ref(v_f_1761_);
                            v_snd_1805_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1812_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1812_ == 0 {
                                v_unused_1813_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                                crate::leanh::lean_dec(v_unused_1813_);
                                v___x_1807_ = v___x_1766_;
                                v_isShared_1808_ = v_isSharedCheck_1812_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1805_);
                                crate::leanh::lean_dec(v___x_1766_);
                                v___x_1807_ = crate::leanh::lean_box(0);
                                v_isShared_1808_ = v_isSharedCheck_1812_;
                                state = 9;
                                continue;
                            }
                        }
                        4 => {
                            crate::leanh::lean_dec_ref(v_f_1761_);
                            v_snd_1814_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1821_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1821_ == 0 {
                                v_unused_1822_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                                crate::leanh::lean_dec(v_unused_1822_);
                                v___x_1816_ = v___x_1766_;
                                v_isShared_1817_ = v_isSharedCheck_1821_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1814_);
                                crate::leanh::lean_dec(v___x_1766_);
                                v___x_1816_ = crate::leanh::lean_box(0);
                                v_isShared_1817_ = v_isSharedCheck_1821_;
                                state = 11;
                                continue;
                            }
                        }
                        3 => {
                            crate::leanh::lean_dec_ref(v_f_1761_);
                            v_snd_1823_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1830_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1830_ == 0 {
                                v_unused_1831_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                                crate::leanh::lean_dec(v_unused_1831_);
                                v___x_1825_ = v___x_1766_;
                                v_isShared_1826_ = v_isSharedCheck_1830_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1823_);
                                crate::leanh::lean_dec(v___x_1766_);
                                v___x_1825_ = crate::leanh::lean_box(0);
                                v_isShared_1826_ = v_isSharedCheck_1830_;
                                state = 13;
                                continue;
                            }
                        }
                        _ => {
                            v_snd_1832_ = crate::leanh::lean_ctor_get(v___x_1766_, 1);
                            crate::leanh::lean_inc(v_snd_1832_);
                            crate::leanh::lean_dec_ref(v___x_1766_);
                            v___x_1833_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS_x27___closed__1),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_replaceS_x27___closed__1_once
                                ),
                                _init_l_Lean_Meta_Sym_replaceS_x27___closed__1,
                            );
                            v___x_1834_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(
                                v_e_1760_,
                                v___x_1764_,
                                v_f_1761_,
                                v___x_1833_,
                                v_a_1762_,
                                v_snd_1832_,
                            );
                            v_fst_1835_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                            crate::leanh::lean_inc(v_fst_1835_);
                            v_snd_1836_ = crate::leanh::lean_ctor_get(v___x_1834_, 1);
                            crate::leanh::lean_inc(v_snd_1836_);
                            crate::leanh::lean_dec_ref(v___x_1834_);
                            v_fst_1837_ = crate::leanh::lean_ctor_get(v_fst_1835_, 0);
                            v_isSharedCheck_1844_ =
                                (!crate::leanh::lean_is_exclusive(v_fst_1835_)) as u8;
                            if v_isSharedCheck_1844_ == 0 {
                                v_unused_1845_ = crate::leanh::lean_ctor_get(v_fst_1835_, 1);
                                crate::leanh::lean_dec(v_unused_1845_);
                                v___x_1839_ = v_fst_1835_;
                                v_isShared_1840_ = v_isSharedCheck_1844_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_fst_1837_);
                                crate::leanh::lean_dec(v_fst_1835_);
                                v___x_1839_ = crate::leanh::lean_box(0);
                                v_isShared_1840_ = v_isSharedCheck_1844_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_val_1772_ = crate::leanh::lean_ctor_get(v_fst_1767_, 0);
                crate::leanh::lean_inc(v_val_1772_);
                crate::leanh::lean_dec_ref_known(v_fst_1767_, 1);
                if v_isShared_1771_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1770_, 0, v_val_1772_);
                    v___x_1774_ = v___x_1770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1775_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_val_1772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_snd_1768_);
                    v___x_1774_ = v_reuseFailAlloc_1775_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1774_;
            }
            3 => {
                if v_isShared_1781_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1780_, 0, v_e_1760_);
                    v___x_1783_ = v___x_1780_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_e_1760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_snd_1778_);
                    v___x_1783_ = v_reuseFailAlloc_1784_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1783_;
            }
            5 => {
                if v_isShared_1790_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1789_, 0, v_e_1760_);
                    v___x_1792_ = v___x_1789_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_e_1760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_snd_1787_);
                    v___x_1792_ = v_reuseFailAlloc_1793_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1792_;
            }
            7 => {
                if v_isShared_1799_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1798_, 0, v_e_1760_);
                    v___x_1801_ = v___x_1798_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_e_1760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_snd_1796_);
                    v___x_1801_ = v_reuseFailAlloc_1802_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1801_;
            }
            9 => {
                if v_isShared_1808_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1807_, 0, v_e_1760_);
                    v___x_1810_ = v___x_1807_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_e_1760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_snd_1805_);
                    v___x_1810_ = v_reuseFailAlloc_1811_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1810_;
            }
            11 => {
                if v_isShared_1817_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1816_, 0, v_e_1760_);
                    v___x_1819_ = v___x_1816_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_e_1760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_snd_1814_);
                    v___x_1819_ = v_reuseFailAlloc_1820_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1819_;
            }
            13 => {
                if v_isShared_1826_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1825_, 0, v_e_1760_);
                    v___x_1828_ = v___x_1825_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_e_1760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_snd_1823_);
                    v___x_1828_ = v_reuseFailAlloc_1829_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1828_;
            }
            15 => {
                if v_isShared_1840_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1839_, 1, v_snd_1836_);
                    v___x_1842_ = v___x_1839_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_fst_1837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_snd_1836_);
                    v___x_1842_ = v_reuseFailAlloc_1843_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_replaceS_x27___boxed(
    mut v_e_1846_: *mut crate::leanh::LeanObject,
    mut v_f_1847_: *mut crate::leanh::LeanObject,
    mut v_a_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1850_: u8 = 0;
    let mut v_res_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1850_ = (crate::leanh::lean_unbox(v_a_1848_) as u8);
    v_res_1851_ = l_Lean_Meta_Sym_replaceS_x27(v_e_1846_, v_f_1847_, v_a_boxed_1850_, v_a_1849_);
    return v_res_1851_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___f_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1854_ = l_Lean_Meta_Sym_replaceS___redArg___closed__1;
    v___f_1855_ = l_Lean_Meta_Sym_replaceS___redArg___closed__0;
    v___x_1856_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1855_,
        v___f_1854_,
    );
    return v___x_1856_;
}
pub unsafe fn l_Lean_Meta_Sym_replaceS___redArg(
    mut v_e_1857_: *mut crate::leanh::LeanObject,
    mut v_f_1858_: *mut crate::leanh::LeanObject,
    mut v_a_1859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1872_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1894_: u8 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1897_: u8 = 0;
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_unused_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1905_: u8 = 0;
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1861_ = lean_st_ref_take(v_a_1859_);
                v_share_1862_ = crate::leanh::lean_ctor_get(v___x_1861_, 0);
                v_maxFVar_1863_ = crate::leanh::lean_ctor_get(v___x_1861_, 1);
                v_proofInstInfo_1864_ = crate::leanh::lean_ctor_get(v___x_1861_, 2);
                v_inferType_1865_ = crate::leanh::lean_ctor_get(v___x_1861_, 3);
                v_getLevel_1866_ = crate::leanh::lean_ctor_get(v___x_1861_, 4);
                v_congrInfo_1867_ = crate::leanh::lean_ctor_get(v___x_1861_, 5);
                v_defEqI_1868_ = crate::leanh::lean_ctor_get(v___x_1861_, 6);
                v_extensions_1869_ = crate::leanh::lean_ctor_get(v___x_1861_, 7);
                v_issues_1870_ = crate::leanh::lean_ctor_get(v___x_1861_, 8);
                v_canon_1871_ = crate::leanh::lean_ctor_get(v___x_1861_, 9);
                v_debug_1872_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1861_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1925_ = (!crate::leanh::lean_is_exclusive(v___x_1861_)) as u8;
                if v_isSharedCheck_1925_ == 0 {
                    v___x_1874_ = v___x_1861_;
                    v_isShared_1875_ = v_isSharedCheck_1925_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1871_);
                    crate::leanh::lean_inc(v_issues_1870_);
                    crate::leanh::lean_inc(v_extensions_1869_);
                    crate::leanh::lean_inc(v_defEqI_1868_);
                    crate::leanh::lean_inc(v_congrInfo_1867_);
                    crate::leanh::lean_inc(v_getLevel_1866_);
                    crate::leanh::lean_inc(v_inferType_1865_);
                    crate::leanh::lean_inc(v_proofInstInfo_1864_);
                    crate::leanh::lean_inc(v_maxFVar_1863_);
                    crate::leanh::lean_inc(v_share_1862_);
                    crate::leanh::lean_dec(v___x_1861_);
                    v___x_1874_ = crate::leanh::lean_box(0);
                    v_isShared_1875_ = v_isSharedCheck_1925_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1876_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS___redArg___closed__2_once),
                    _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2,
                );
                if v_isShared_1875_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1874_, 0, v___x_1876_);
                    v___x_1878_ = v___x_1874_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1924_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_maxFVar_1863_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_proofInstInfo_1864_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_inferType_1865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 4, v_getLevel_1866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 5, v_congrInfo_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 6, v_defEqI_1868_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 7, v_extensions_1869_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 8, v_issues_1870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 9, v_canon_1871_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1924_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1872_,
                    );
                    v___x_1878_ = v_reuseFailAlloc_1924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1879_ = lean_st_ref_set(v_a_1859_, v___x_1878_);
                v___x_1880_ = lean_st_ref_get(v_a_1859_);
                v_debug_1905_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1880_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_1880_);
                v___x_1906_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1907_ = crate::leanh::lean_box((v_debug_1905_) as usize);
                crate::leanh::lean_inc_ref(v_f_1858_);
                crate::leanh::lean_inc_ref(v_e_1857_);
                v___x_1908_ = crate::leanh::lean_apply_4(
                    v_f_1858_,
                    v_e_1857_,
                    v___x_1906_,
                    v___x_1907_,
                    v_share_1862_,
                );
                v_fst_1909_ = crate::leanh::lean_ctor_get(v___x_1908_, 0);
                crate::leanh::lean_inc(v_fst_1909_);
                if crate::leanh::lean_obj_tag(v_fst_1909_) == 1 {
                    crate::leanh::lean_dec_ref(v_f_1858_);
                    crate::leanh::lean_dec_ref(v_e_1857_);
                    v_snd_1910_ = crate::leanh::lean_ctor_get(v___x_1908_, 1);
                    crate::leanh::lean_inc(v_snd_1910_);
                    crate::leanh::lean_dec_ref(v___x_1908_);
                    v_val_1911_ = crate::leanh::lean_ctor_get(v_fst_1909_, 0);
                    crate::leanh::lean_inc(v_val_1911_);
                    crate::leanh::lean_dec_ref_known(v_fst_1909_, 1);
                    v_fst_1882_ = v_val_1911_;
                    v_snd_1883_ = v_snd_1910_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1909_);
                    match crate::leanh::lean_obj_tag(v_e_1857_) {
                        9 => {
                            crate::leanh::lean_dec_ref(v_f_1858_);
                            v_snd_1912_ = crate::leanh::lean_ctor_get(v___x_1908_, 1);
                            crate::leanh::lean_inc(v_snd_1912_);
                            crate::leanh::lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1912_;
                            state = 3;
                            continue;
                        }
                        2 => {
                            crate::leanh::lean_dec_ref(v_f_1858_);
                            v_snd_1913_ = crate::leanh::lean_ctor_get(v___x_1908_, 1);
                            crate::leanh::lean_inc(v_snd_1913_);
                            crate::leanh::lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1913_;
                            state = 3;
                            continue;
                        }
                        0 => {
                            crate::leanh::lean_dec_ref(v_f_1858_);
                            v_snd_1914_ = crate::leanh::lean_ctor_get(v___x_1908_, 1);
                            crate::leanh::lean_inc(v_snd_1914_);
                            crate::leanh::lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1914_;
                            state = 3;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec_ref(v_f_1858_);
                            v_snd_1915_ = crate::leanh::lean_ctor_get(v___x_1908_, 1);
                            crate::leanh::lean_inc(v_snd_1915_);
                            crate::leanh::lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1915_;
                            state = 3;
                            continue;
                        }
                        4 => {
                            crate::leanh::lean_dec_ref(v_f_1858_);
                            v_snd_1916_ = crate::leanh::lean_ctor_get(v___x_1908_, 1);
                            crate::leanh::lean_inc(v_snd_1916_);
                            crate::leanh::lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1916_;
                            state = 3;
                            continue;
                        }
                        3 => {
                            crate::leanh::lean_dec_ref(v_f_1858_);
                            v_snd_1917_ = crate::leanh::lean_ctor_get(v___x_1908_, 1);
                            crate::leanh::lean_inc(v_snd_1917_);
                            crate::leanh::lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1917_;
                            state = 3;
                            continue;
                        }
                        _ => {
                            v_snd_1918_ = crate::leanh::lean_ctor_get(v___x_1908_, 1);
                            crate::leanh::lean_inc(v_snd_1918_);
                            crate::leanh::lean_dec_ref(v___x_1908_);
                            v___x_1919_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS_x27___closed__1),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_replaceS_x27___closed__1_once
                                ),
                                _init_l_Lean_Meta_Sym_replaceS_x27___closed__1,
                            );
                            v___x_1920_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(
                                v_e_1857_,
                                v___x_1906_,
                                v_f_1858_,
                                v___x_1919_,
                                v_debug_1905_,
                                v_snd_1918_,
                            );
                            v_fst_1921_ = crate::leanh::lean_ctor_get(v___x_1920_, 0);
                            crate::leanh::lean_inc(v_fst_1921_);
                            v_snd_1922_ = crate::leanh::lean_ctor_get(v___x_1920_, 1);
                            crate::leanh::lean_inc(v_snd_1922_);
                            crate::leanh::lean_dec_ref(v___x_1920_);
                            v_fst_1923_ = crate::leanh::lean_ctor_get(v_fst_1921_, 0);
                            crate::leanh::lean_inc(v_fst_1923_);
                            crate::leanh::lean_dec(v_fst_1921_);
                            v_fst_1882_ = v_fst_1923_;
                            v_snd_1883_ = v_snd_1922_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_1884_ = lean_st_ref_take(v_a_1859_);
                v_maxFVar_1885_ = crate::leanh::lean_ctor_get(v___x_1884_, 1);
                v_proofInstInfo_1886_ = crate::leanh::lean_ctor_get(v___x_1884_, 2);
                v_inferType_1887_ = crate::leanh::lean_ctor_get(v___x_1884_, 3);
                v_getLevel_1888_ = crate::leanh::lean_ctor_get(v___x_1884_, 4);
                v_congrInfo_1889_ = crate::leanh::lean_ctor_get(v___x_1884_, 5);
                v_defEqI_1890_ = crate::leanh::lean_ctor_get(v___x_1884_, 6);
                v_extensions_1891_ = crate::leanh::lean_ctor_get(v___x_1884_, 7);
                v_issues_1892_ = crate::leanh::lean_ctor_get(v___x_1884_, 8);
                v_canon_1893_ = crate::leanh::lean_ctor_get(v___x_1884_, 9);
                v_debug_1894_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1884_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1903_ = (!crate::leanh::lean_is_exclusive(v___x_1884_)) as u8;
                if v_isSharedCheck_1903_ == 0 {
                    v_unused_1904_ = crate::leanh::lean_ctor_get(v___x_1884_, 0);
                    crate::leanh::lean_dec(v_unused_1904_);
                    v___x_1896_ = v___x_1884_;
                    v_isShared_1897_ = v_isSharedCheck_1903_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1893_);
                    crate::leanh::lean_inc(v_issues_1892_);
                    crate::leanh::lean_inc(v_extensions_1891_);
                    crate::leanh::lean_inc(v_defEqI_1890_);
                    crate::leanh::lean_inc(v_congrInfo_1889_);
                    crate::leanh::lean_inc(v_getLevel_1888_);
                    crate::leanh::lean_inc(v_inferType_1887_);
                    crate::leanh::lean_inc(v_proofInstInfo_1886_);
                    crate::leanh::lean_inc(v_maxFVar_1885_);
                    crate::leanh::lean_dec(v___x_1884_);
                    v___x_1896_ = crate::leanh::lean_box(0);
                    v_isShared_1897_ = v_isSharedCheck_1903_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1897_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1896_, 0, v_snd_1883_);
                    v___x_1899_ = v___x_1896_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_snd_1883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_maxFVar_1885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_proofInstInfo_1886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_inferType_1887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_getLevel_1888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 5, v_congrInfo_1889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 6, v_defEqI_1890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 7, v_extensions_1891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 8, v_issues_1892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 9, v_canon_1893_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1902_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1894_,
                    );
                    v___x_1899_ = v_reuseFailAlloc_1902_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1900_ = lean_st_ref_set(v_a_1859_, v___x_1899_);
                v___x_1901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1901_, 0, v_fst_1882_);
                return v___x_1901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_replaceS___redArg___boxed(
    mut v_e_1926_: *mut crate::leanh::LeanObject,
    mut v_f_1927_: *mut crate::leanh::LeanObject,
    mut v_a_1928_: *mut crate::leanh::LeanObject,
    mut v_a_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ = l_Lean_Meta_Sym_replaceS___redArg(v_e_1926_, v_f_1927_, v_a_1928_);
    crate::leanh::lean_dec(v_a_1928_);
    return v_res_1930_;
}
pub unsafe fn l_Lean_Meta_Sym_replaceS(
    mut v_e_1931_: *mut crate::leanh::LeanObject,
    mut v_f_1932_: *mut crate::leanh::LeanObject,
    mut v_a_1933_: *mut crate::leanh::LeanObject,
    mut v_a_1934_: *mut crate::leanh::LeanObject,
    mut v_a_1935_: *mut crate::leanh::LeanObject,
    mut v_a_1936_: *mut crate::leanh::LeanObject,
    mut v_a_1937_: *mut crate::leanh::LeanObject,
    mut v_a_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1951_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1954_: u8 = 0;
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1973_: u8 = 0;
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut v_unused_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1984_: u8 = 0;
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1940_ = lean_st_ref_take(v_a_1934_);
                v_share_1941_ = crate::leanh::lean_ctor_get(v___x_1940_, 0);
                v_maxFVar_1942_ = crate::leanh::lean_ctor_get(v___x_1940_, 1);
                v_proofInstInfo_1943_ = crate::leanh::lean_ctor_get(v___x_1940_, 2);
                v_inferType_1944_ = crate::leanh::lean_ctor_get(v___x_1940_, 3);
                v_getLevel_1945_ = crate::leanh::lean_ctor_get(v___x_1940_, 4);
                v_congrInfo_1946_ = crate::leanh::lean_ctor_get(v___x_1940_, 5);
                v_defEqI_1947_ = crate::leanh::lean_ctor_get(v___x_1940_, 6);
                v_extensions_1948_ = crate::leanh::lean_ctor_get(v___x_1940_, 7);
                v_issues_1949_ = crate::leanh::lean_ctor_get(v___x_1940_, 8);
                v_canon_1950_ = crate::leanh::lean_ctor_get(v___x_1940_, 9);
                v_debug_1951_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1940_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2004_ = (!crate::leanh::lean_is_exclusive(v___x_1940_)) as u8;
                if v_isSharedCheck_2004_ == 0 {
                    v___x_1953_ = v___x_1940_;
                    v_isShared_1954_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1950_);
                    crate::leanh::lean_inc(v_issues_1949_);
                    crate::leanh::lean_inc(v_extensions_1948_);
                    crate::leanh::lean_inc(v_defEqI_1947_);
                    crate::leanh::lean_inc(v_congrInfo_1946_);
                    crate::leanh::lean_inc(v_getLevel_1945_);
                    crate::leanh::lean_inc(v_inferType_1944_);
                    crate::leanh::lean_inc(v_proofInstInfo_1943_);
                    crate::leanh::lean_inc(v_maxFVar_1942_);
                    crate::leanh::lean_inc(v_share_1941_);
                    crate::leanh::lean_dec(v___x_1940_);
                    v___x_1953_ = crate::leanh::lean_box(0);
                    v_isShared_1954_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1955_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS___redArg___closed__2_once),
                    _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2,
                );
                if v_isShared_1954_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1953_, 0, v___x_1955_);
                    v___x_1957_ = v___x_1953_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_maxFVar_1942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_proofInstInfo_1943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_inferType_1944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_getLevel_1945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 5, v_congrInfo_1946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 6, v_defEqI_1947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 7, v_extensions_1948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 8, v_issues_1949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 9, v_canon_1950_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2003_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1951_,
                    );
                    v___x_1957_ = v_reuseFailAlloc_2003_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1958_ = lean_st_ref_set(v_a_1934_, v___x_1957_);
                v___x_1959_ = lean_st_ref_get(v_a_1934_);
                v_debug_1984_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1959_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_1959_);
                v___x_1985_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1986_ = crate::leanh::lean_box((v_debug_1984_) as usize);
                crate::leanh::lean_inc_ref(v_f_1932_);
                crate::leanh::lean_inc_ref(v_e_1931_);
                v___x_1987_ = crate::leanh::lean_apply_4(
                    v_f_1932_,
                    v_e_1931_,
                    v___x_1985_,
                    v___x_1986_,
                    v_share_1941_,
                );
                v_fst_1988_ = crate::leanh::lean_ctor_get(v___x_1987_, 0);
                crate::leanh::lean_inc(v_fst_1988_);
                if crate::leanh::lean_obj_tag(v_fst_1988_) == 1 {
                    crate::leanh::lean_dec_ref(v_f_1932_);
                    crate::leanh::lean_dec_ref(v_e_1931_);
                    v_snd_1989_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                    crate::leanh::lean_inc(v_snd_1989_);
                    crate::leanh::lean_dec_ref(v___x_1987_);
                    v_val_1990_ = crate::leanh::lean_ctor_get(v_fst_1988_, 0);
                    crate::leanh::lean_inc(v_val_1990_);
                    crate::leanh::lean_dec_ref_known(v_fst_1988_, 1);
                    v_fst_1961_ = v_val_1990_;
                    v_snd_1962_ = v_snd_1989_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1988_);
                    match crate::leanh::lean_obj_tag(v_e_1931_) {
                        9 => {
                            crate::leanh::lean_dec_ref(v_f_1932_);
                            v_snd_1991_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                            crate::leanh::lean_inc(v_snd_1991_);
                            crate::leanh::lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1991_;
                            state = 3;
                            continue;
                        }
                        2 => {
                            crate::leanh::lean_dec_ref(v_f_1932_);
                            v_snd_1992_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                            crate::leanh::lean_inc(v_snd_1992_);
                            crate::leanh::lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1992_;
                            state = 3;
                            continue;
                        }
                        0 => {
                            crate::leanh::lean_dec_ref(v_f_1932_);
                            v_snd_1993_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                            crate::leanh::lean_inc(v_snd_1993_);
                            crate::leanh::lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1993_;
                            state = 3;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec_ref(v_f_1932_);
                            v_snd_1994_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                            crate::leanh::lean_inc(v_snd_1994_);
                            crate::leanh::lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1994_;
                            state = 3;
                            continue;
                        }
                        4 => {
                            crate::leanh::lean_dec_ref(v_f_1932_);
                            v_snd_1995_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                            crate::leanh::lean_inc(v_snd_1995_);
                            crate::leanh::lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1995_;
                            state = 3;
                            continue;
                        }
                        3 => {
                            crate::leanh::lean_dec_ref(v_f_1932_);
                            v_snd_1996_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                            crate::leanh::lean_inc(v_snd_1996_);
                            crate::leanh::lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1996_;
                            state = 3;
                            continue;
                        }
                        _ => {
                            v_snd_1997_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                            crate::leanh::lean_inc(v_snd_1997_);
                            crate::leanh::lean_dec_ref(v___x_1987_);
                            v___x_1998_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS_x27___closed__1),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_replaceS_x27___closed__1_once
                                ),
                                _init_l_Lean_Meta_Sym_replaceS_x27___closed__1,
                            );
                            v___x_1999_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(
                                v_e_1931_,
                                v___x_1985_,
                                v_f_1932_,
                                v___x_1998_,
                                v_debug_1984_,
                                v_snd_1997_,
                            );
                            v_fst_2000_ = crate::leanh::lean_ctor_get(v___x_1999_, 0);
                            crate::leanh::lean_inc(v_fst_2000_);
                            v_snd_2001_ = crate::leanh::lean_ctor_get(v___x_1999_, 1);
                            crate::leanh::lean_inc(v_snd_2001_);
                            crate::leanh::lean_dec_ref(v___x_1999_);
                            v_fst_2002_ = crate::leanh::lean_ctor_get(v_fst_2000_, 0);
                            crate::leanh::lean_inc(v_fst_2002_);
                            crate::leanh::lean_dec(v_fst_2000_);
                            v_fst_1961_ = v_fst_2002_;
                            v_snd_1962_ = v_snd_2001_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_1963_ = lean_st_ref_take(v_a_1934_);
                v_maxFVar_1964_ = crate::leanh::lean_ctor_get(v___x_1963_, 1);
                v_proofInstInfo_1965_ = crate::leanh::lean_ctor_get(v___x_1963_, 2);
                v_inferType_1966_ = crate::leanh::lean_ctor_get(v___x_1963_, 3);
                v_getLevel_1967_ = crate::leanh::lean_ctor_get(v___x_1963_, 4);
                v_congrInfo_1968_ = crate::leanh::lean_ctor_get(v___x_1963_, 5);
                v_defEqI_1969_ = crate::leanh::lean_ctor_get(v___x_1963_, 6);
                v_extensions_1970_ = crate::leanh::lean_ctor_get(v___x_1963_, 7);
                v_issues_1971_ = crate::leanh::lean_ctor_get(v___x_1963_, 8);
                v_canon_1972_ = crate::leanh::lean_ctor_get(v___x_1963_, 9);
                v_debug_1973_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1963_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1982_ = (!crate::leanh::lean_is_exclusive(v___x_1963_)) as u8;
                if v_isSharedCheck_1982_ == 0 {
                    v_unused_1983_ = crate::leanh::lean_ctor_get(v___x_1963_, 0);
                    crate::leanh::lean_dec(v_unused_1983_);
                    v___x_1975_ = v___x_1963_;
                    v_isShared_1976_ = v_isSharedCheck_1982_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1972_);
                    crate::leanh::lean_inc(v_issues_1971_);
                    crate::leanh::lean_inc(v_extensions_1970_);
                    crate::leanh::lean_inc(v_defEqI_1969_);
                    crate::leanh::lean_inc(v_congrInfo_1968_);
                    crate::leanh::lean_inc(v_getLevel_1967_);
                    crate::leanh::lean_inc(v_inferType_1966_);
                    crate::leanh::lean_inc(v_proofInstInfo_1965_);
                    crate::leanh::lean_inc(v_maxFVar_1964_);
                    crate::leanh::lean_dec(v___x_1963_);
                    v___x_1975_ = crate::leanh::lean_box(0);
                    v_isShared_1976_ = v_isSharedCheck_1982_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1975_, 0, v_snd_1962_);
                    v___x_1978_ = v___x_1975_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_snd_1962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_maxFVar_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_proofInstInfo_1965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_inferType_1966_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_getLevel_1967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_congrInfo_1968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_defEqI_1969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_extensions_1970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_issues_1971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 9, v_canon_1972_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1981_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1973_,
                    );
                    v___x_1978_ = v_reuseFailAlloc_1981_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1979_ = lean_st_ref_set(v_a_1934_, v___x_1978_);
                v___x_1980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1980_, 0, v_fst_1961_);
                return v___x_1980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_replaceS___boxed(
    mut v_e_2005_: *mut crate::leanh::LeanObject,
    mut v_f_2006_: *mut crate::leanh::LeanObject,
    mut v_a_2007_: *mut crate::leanh::LeanObject,
    mut v_a_2008_: *mut crate::leanh::LeanObject,
    mut v_a_2009_: *mut crate::leanh::LeanObject,
    mut v_a_2010_: *mut crate::leanh::LeanObject,
    mut v_a_2011_: *mut crate::leanh::LeanObject,
    mut v_a_2012_: *mut crate::leanh::LeanObject,
    mut v_a_2013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2014_ = l_Lean_Meta_Sym_replaceS(
        v_e_2005_, v_f_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_,
    );
    crate::leanh::lean_dec(v_a_2012_);
    crate::leanh::lean_dec_ref(v_a_2011_);
    crate::leanh::lean_dec(v_a_2010_);
    crate::leanh::lean_dec_ref(v_a_2009_);
    crate::leanh::lean_dec(v_a_2008_);
    crate::leanh::lean_dec_ref(v_a_2007_);
    return v_res_2014_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_ReplaceS(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_ReplaceS(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_ReplaceS(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_ReplaceS(builtin);
}
