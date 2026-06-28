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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_uint64_mix_hash,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashableProd___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_bind as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_pure as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_map as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_value
)
    as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35_value:
    LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34_value:
    LeanStringObject<54> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33_value
)
    as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_replaceS_x27___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_replaceS_x27___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_replaceS_x27___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_replaceS_x27___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_replaceS___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_replaceS___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_replaceS___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_replaceS___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_replaceS___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_replaceS___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_replaceS___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_replaceS___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(
    mut v_a_1008_: *mut LeanObject,
    mut v_x_1009_: *mut LeanObject,
) -> u8 {
    let mut v___x_1010_: u8 = 0;
    let mut v_key_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1014_: u8 = 0;
    let mut v_fst_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1009_) == 0 {
                    v___x_1010_ = 0;
                    return v___x_1010_;
                } else {
                    v_key_1011_ = lean_ctor_get(v_x_1009_, 0);
                    v_tail_1012_ = lean_ctor_get(v_x_1009_, 2);
                    v_fst_1016_ = lean_ctor_get(v_key_1011_, 0);
                    v_snd_1017_ = lean_ctor_get(v_key_1011_, 1);
                    v_fst_1018_ = lean_ctor_get(v_a_1008_, 0);
                    v_snd_1019_ = lean_ctor_get(v_a_1008_, 1);
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
    mut v_a_1022_: *mut LeanObject,
    mut v_x_1023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1024_: u8 = 0;
    let mut v_r_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1024_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1022_, v_x_1023_);
    lean_dec(v_x_1023_);
    lean_dec_ref(v_a_1022_);
    v_r_1025_ = lean_box((v_res_1024_) as usize);
    return v_r_1025_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1026_: *mut LeanObject,
    mut v_x_1027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1033_: u8 = 0;
    let mut v_fst_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1027_) == 0 {
                    return v_x_1026_;
                } else {
                    v_key_1028_ = lean_ctor_get(v_x_1027_, 0);
                    v_value_1029_ = lean_ctor_get(v_x_1027_, 1);
                    v_tail_1030_ = lean_ctor_get(v_x_1027_, 2);
                    v_isSharedCheck_1057_ = (!lean_is_exclusive(v_x_1027_)) as u8;
                    if v_isSharedCheck_1057_ == 0 {
                        v___x_1032_ = v_x_1027_;
                        v_isShared_1033_ = v_isSharedCheck_1057_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1030_);
                        lean_inc(v_value_1029_);
                        lean_inc(v_key_1028_);
                        lean_dec(v_x_1027_);
                        v___x_1032_ = lean_box(0);
                        v_isShared_1033_ = v_isSharedCheck_1057_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1034_ = lean_ctor_get(v_key_1028_, 0);
                v_snd_1035_ = lean_ctor_get(v_key_1028_, 1);
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
                lean_inc(v___x_1051_);
                if v_isShared_1033_ == 0 {
                    lean_ctor_set(v___x_1032_, 2, v___x_1051_);
                    v___x_1053_ = v___x_1032_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_key_1028_);
                    lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_value_1029_);
                    lean_ctor_set(v_reuseFailAlloc_1056_, 2, v___x_1051_);
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
    mut v_i_1058_: *mut LeanObject,
    mut v_source_1059_: *mut LeanObject,
    mut v_target_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: u8 = 0;
    let mut v_es_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1061_ = lean_array_get_size(v_source_1059_);
                v___x_1062_ = lean_nat_dec_lt(v_i_1058_, v___x_1061_);
                if v___x_1062_ == 0 {
                    lean_dec_ref(v_source_1059_);
                    lean_dec(v_i_1058_);
                    return v_target_1060_;
                } else {
                    v_es_1063_ = lean_array_fget(v_source_1059_, v_i_1058_);
                    v___x_1064_ = lean_box(0);
                    v_source_1065_ = lean_array_fset(v_source_1059_, v_i_1058_, v___x_1064_);
                    v_target_1066_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1060_, v_es_1063_);
                    v___x_1067_ = lean_unsigned_to_nat(1);
                    v___x_1068_ = lean_nat_add(v_i_1058_, v___x_1067_);
                    lean_dec(v_i_1058_);
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
    mut v_data_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    v___x_1071_ = lean_array_get_size(v_data_1070_);
    v___x_1072_ = lean_unsigned_to_nat(2);
    v_nbuckets_1073_ = lean_nat_mul(v___x_1071_, v___x_1072_);
    v___x_1074_ = lean_unsigned_to_nat(0);
    v___x_1075_ = lean_box(0);
    v___x_1076_ = lean_mk_array(v_nbuckets_1073_, v___x_1075_);
    v___x_1077_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1074_, v_data_1070_, v___x_1076_);
    return v___x_1077_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(
    mut v_a_1078_: *mut LeanObject,
    mut v_b_1079_: *mut LeanObject,
    mut v_x_1080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1086_: u8 = 0;
    let mut v___y_1088_: u8 = 0;
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: u8 = 0;
    let mut v___x_1101_: u8 = 0;
    let mut v_isSharedCheck_1102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1080_) == 0 {
                    lean_dec(v_b_1079_);
                    lean_dec_ref(v_a_1078_);
                    return v_x_1080_;
                } else {
                    v_key_1081_ = lean_ctor_get(v_x_1080_, 0);
                    v_value_1082_ = lean_ctor_get(v_x_1080_, 1);
                    v_tail_1083_ = lean_ctor_get(v_x_1080_, 2);
                    v_isSharedCheck_1102_ = (!lean_is_exclusive(v_x_1080_)) as u8;
                    if v_isSharedCheck_1102_ == 0 {
                        v___x_1085_ = v_x_1080_;
                        v_isShared_1086_ = v_isSharedCheck_1102_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1083_);
                        lean_inc(v_value_1082_);
                        lean_inc(v_key_1081_);
                        lean_dec(v_x_1080_);
                        v___x_1085_ = lean_box(0);
                        v_isShared_1086_ = v_isSharedCheck_1102_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1096_ = lean_ctor_get(v_key_1081_, 0);
                v_snd_1097_ = lean_ctor_get(v_key_1081_, 1);
                v_fst_1098_ = lean_ctor_get(v_a_1078_, 0);
                v_snd_1099_ = lean_ctor_get(v_a_1078_, 1);
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
                        lean_ctor_set(v___x_1085_, 2, v___x_1089_);
                        v___x_1091_ = v___x_1085_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_key_1081_);
                        lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_value_1082_);
                        lean_ctor_set(v_reuseFailAlloc_1092_, 2, v___x_1089_);
                        v___x_1091_ = v_reuseFailAlloc_1092_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1082_);
                    lean_dec(v_key_1081_);
                    if v_isShared_1086_ == 0 {
                        lean_ctor_set(v___x_1085_, 1, v_b_1079_);
                        lean_ctor_set(v___x_1085_, 0, v_a_1078_);
                        v___x_1094_ = v___x_1085_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1078_);
                        lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_b_1079_);
                        lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_tail_1083_);
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
    mut v_m_1103_: *mut LeanObject,
    mut v_a_1104_: *mut LeanObject,
    mut v_b_1105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v_fst_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: u8 = 0;
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: u8 = 0;
    let mut v_val_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1106_ = lean_ctor_get(v_m_1103_, 0);
                v_buckets_1107_ = lean_ctor_get(v_m_1103_, 1);
                v_isSharedCheck_1154_ = (!lean_is_exclusive(v_m_1103_)) as u8;
                if v_isSharedCheck_1154_ == 0 {
                    v___x_1109_ = v_m_1103_;
                    v_isShared_1110_ = v_isSharedCheck_1154_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1107_);
                    lean_inc(v_size_1106_);
                    lean_dec(v_m_1103_);
                    v___x_1109_ = lean_box(0);
                    v_isShared_1110_ = v_isSharedCheck_1154_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1111_ = lean_ctor_get(v_a_1104_, 0);
                v_snd_1112_ = lean_ctor_get(v_a_1104_, 1);
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
                    v___x_1130_ = lean_unsigned_to_nat(1);
                    v_size_x27_1131_ = lean_nat_add(v_size_1106_, v___x_1130_);
                    lean_dec(v_size_1106_);
                    lean_inc(v_bkt_1128_);
                    v___x_1132_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1132_, 0, v_a_1104_);
                    lean_ctor_set(v___x_1132_, 1, v_b_1105_);
                    lean_ctor_set(v___x_1132_, 2, v_bkt_1128_);
                    v_buckets_x27_1133_ =
                        lean_array_uset(v_buckets_1107_, v___x_1127_, v___x_1132_);
                    v___x_1134_ = lean_unsigned_to_nat(4);
                    v___x_1135_ = lean_nat_mul(v_size_x27_1131_, v___x_1134_);
                    v___x_1136_ = lean_unsigned_to_nat(3);
                    v___x_1137_ = lean_nat_div(v___x_1135_, v___x_1136_);
                    lean_dec(v___x_1135_);
                    v___x_1138_ = lean_array_get_size(v_buckets_x27_1133_);
                    v___x_1139_ = lean_nat_dec_le(v___x_1137_, v___x_1138_);
                    lean_dec(v___x_1137_);
                    if v___x_1139_ == 0 {
                        v_val_1140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1133_);
                        if v_isShared_1110_ == 0 {
                            lean_ctor_set(v___x_1109_, 1, v_val_1140_);
                            lean_ctor_set(v___x_1109_, 0, v_size_x27_1131_);
                            v___x_1142_ = v___x_1109_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_size_x27_1131_);
                            lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_val_1140_);
                            v___x_1142_ = v_reuseFailAlloc_1143_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1110_ == 0 {
                            lean_ctor_set(v___x_1109_, 1, v_buckets_x27_1133_);
                            lean_ctor_set(v___x_1109_, 0, v_size_x27_1131_);
                            v___x_1145_ = v___x_1109_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_size_x27_1131_);
                            lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_buckets_x27_1133_);
                            v___x_1145_ = v_reuseFailAlloc_1146_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1128_);
                    v___x_1147_ = lean_box(0);
                    v_buckets_x27_1148_ =
                        lean_array_uset(v_buckets_1107_, v___x_1127_, v___x_1147_);
                    v___x_1149_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1104_, v_b_1105_, v_bkt_1128_);
                    v___x_1150_ = lean_array_uset(v_buckets_x27_1148_, v___x_1127_, v___x_1149_);
                    if v_isShared_1110_ == 0 {
                        lean_ctor_set(v___x_1109_, 1, v___x_1150_);
                        v___x_1152_ = v___x_1109_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_size_1106_);
                        lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
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
    mut v_key_1155_: *mut LeanObject,
    mut v_r_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
    mut v_a_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_r_1156_);
    v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1157_, v_key_1155_, v_r_1156_);
    v___x_1160_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1160_, 0, v_r_1156_);
    lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    v___x_1161_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1161_, 0, v___x_1160_);
    lean_ctor_set(v___x_1161_, 1, v_a_1158_);
    return v___x_1161_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
    mut v_key_1162_: *mut LeanObject,
    mut v_r_1163_: *mut LeanObject,
    mut v_a_1164_: *mut LeanObject,
    mut v_a_1165_: u8,
    mut v_a_1166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    v___x_1167_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
        v_key_1162_,
        v_r_1163_,
        v_a_1164_,
        v_a_1166_,
    );
    return v___x_1167_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(
    mut v_key_1168_: *mut LeanObject,
    mut v_r_1169_: *mut LeanObject,
    mut v_a_1170_: *mut LeanObject,
    mut v_a_1171_: *mut LeanObject,
    mut v_a_1172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1173_: u8 = 0;
    let mut v_res_1174_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1173_ = (lean_unbox(v_a_1171_) as u8);
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
    mut v_00_u03b2_1175_: *mut LeanObject,
    mut v_m_1176_: *mut LeanObject,
    mut v_a_1177_: *mut LeanObject,
    mut v_b_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    v___x_1179_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1176_, v_a_1177_, v_b_1178_);
    return v___x_1179_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(
    mut v_00_u03b2_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
    mut v_x_1182_: *mut LeanObject,
) -> u8 {
    let mut v___x_1183_: u8 = 0;
    v___x_1183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1181_, v_x_1182_);
    return v___x_1183_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(
    mut v_00_u03b2_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_x_1186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1187_: u8 = 0;
    let mut v_r_1188_: *mut LeanObject = core::ptr::null_mut();
    v_res_1187_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1184_, v_a_1185_, v_x_1186_);
    lean_dec(v_x_1186_);
    lean_dec_ref(v_a_1185_);
    v_r_1188_ = lean_box((v_res_1187_) as usize);
    return v_r_1188_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1(
    mut v_00_u03b2_1189_: *mut LeanObject,
    mut v_data_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1190_);
    return v___x_1191_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2(
    mut v_00_u03b2_1192_: *mut LeanObject,
    mut v_a_1193_: *mut LeanObject,
    mut v_b_1194_: *mut LeanObject,
    mut v_x_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    v___x_1196_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1193_, v_b_1194_, v_x_1195_);
    return v___x_1196_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1197_: *mut LeanObject,
    mut v_i_1198_: *mut LeanObject,
    mut v_source_1199_: *mut LeanObject,
    mut v_target_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    v___x_1201_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1198_, v_source_1199_, v_target_1200_);
    return v___x_1201_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1202_: *mut LeanObject,
    mut v_x_1203_: *mut LeanObject,
    mut v_x_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    v___x_1205_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1203_, v_x_1204_);
    return v___x_1205_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4()
-> *mut LeanObject {
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1213_: *mut LeanObject = core::ptr::null_mut();
    v___x_1212_ = lean_alloc_closure(l_instDecidableEqNat___boxed as *mut core::ffi::c_void, 2, 0);
    v___f_1213_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1213_, 0, v___x_1212_);
    return v___f_1213_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5()
-> *mut LeanObject {
    let mut v___f_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1216_: *mut LeanObject = core::ptr::null_mut();
    v___f_1214_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4,
    );
    v___f_1215_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0;
    v___f_1216_ = lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1216_, 0, v___f_1215_);
    lean_closure_set(v___f_1216_, 1, v___f_1214_);
    return v___f_1216_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20()
-> *mut LeanObject {
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    v___x_1262_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19;
    v___x_1263_ = l_ReaderT_instMonad___redArg(v___x_1262_);
    return v___x_1263_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29()
-> *mut LeanObject {
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    v___x_1264_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___x_1265_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1265_, 0, lean_box(0));
    lean_closure_set(v___x_1265_, 1, lean_box(0));
    lean_closure_set(v___x_1265_, 2, v___x_1264_);
    return v___x_1265_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24()
-> *mut LeanObject {
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1267_: *mut LeanObject = core::ptr::null_mut();
    v___x_1266_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___f_1267_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1267_, 0, v___x_1266_);
    return v___f_1267_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23()
-> *mut LeanObject {
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1269_: *mut LeanObject = core::ptr::null_mut();
    v___x_1268_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___f_1269_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1269_, 0, v___x_1268_);
    return v___f_1269_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22()
-> *mut LeanObject {
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1271_: *mut LeanObject = core::ptr::null_mut();
    v___x_1270_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___f_1271_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1271_, 0, v___x_1270_);
    return v___f_1271_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27()
-> *mut LeanObject {
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v___x_1272_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___x_1273_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1273_, 0, lean_box(0));
    lean_closure_set(v___x_1273_, 1, lean_box(0));
    lean_closure_set(v___x_1273_, 2, v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21()
-> *mut LeanObject {
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1275_: *mut LeanObject = core::ptr::null_mut();
    v___x_1274_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___f_1275_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1275_, 0, v___x_1274_);
    return v___f_1275_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25()
-> *mut LeanObject {
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    v___x_1276_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___x_1277_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1277_, 0, lean_box(0));
    lean_closure_set(v___x_1277_, 1, lean_box(0));
    lean_closure_set(v___x_1277_, 2, v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26()
-> *mut LeanObject {
    let mut v___f_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    v___f_1278_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21,
    );
    v___x_1279_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25,
    );
    v___x_1280_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1280_, 0, v___x_1279_);
    lean_ctor_set(v___x_1280_, 1, v___f_1278_);
    return v___x_1280_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28()
-> *mut LeanObject {
    let mut v___f_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    v___f_1281_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24,
    );
    v___f_1282_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23,
    );
    v___f_1283_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22,
    );
    v___x_1284_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27,
    );
    v___x_1285_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26,
    );
    v___x_1286_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1286_, 0, v___x_1285_);
    lean_ctor_set(v___x_1286_, 1, v___x_1284_);
    lean_ctor_set(v___x_1286_, 2, v___f_1283_);
    lean_ctor_set(v___x_1286_, 3, v___f_1282_);
    lean_ctor_set(v___x_1286_, 4, v___f_1281_);
    return v___x_1286_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30()
-> *mut LeanObject {
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1287_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29,
    );
    v___x_1288_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28,
    );
    v___x_1289_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1289_, 0, v___x_1288_);
    lean_ctor_set(v___x_1289_, 1, v___x_1287_);
    return v___x_1289_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31()
-> *mut LeanObject {
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    v___x_1290_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
    );
    v___x_1291_ = lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1291_, 0, lean_box(0));
    lean_closure_set(v___x_1291_, 1, lean_box(0));
    lean_closure_set(v___x_1291_, 2, v___x_1290_);
    return v___x_1291_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32()
-> *mut LeanObject {
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1292_ = l_Lean_instInhabitedExpr;
    v___x_1293_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v___x_1298_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35;
    v___x_1299_ = lean_unsigned_to_nat(67);
    v___x_1300_ = lean_unsigned_to_nat(35);
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
    mut v_e_1304_: *mut LeanObject,
    mut v_offset_1305_: *mut LeanObject,
    mut v_fn_1306_: *mut LeanObject,
    mut v_a_1307_: *mut LeanObject,
    mut v_a_1308_: u8,
    mut v_a_1309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share1_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v_fst_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v___y_1340_: u8 = 0;
    let mut v___x_10643__overap_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: u8 = 0;
    let mut v___x_1351_: u8 = 0;
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut v_binderName_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1357_: u8 = 0;
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v_fst_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___y_1377_: u8 = 0;
    let mut v___x_10804__overap_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: u8 = 0;
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut v_binderName_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1394_: u8 = 0;
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v_fst_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1412_: u8 = 0;
    let mut v___y_1414_: u8 = 0;
    let mut v___x_10969__overap_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: u8 = 0;
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut v_isSharedCheck_1427_: u8 = 0;
    let mut v_declName_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1432_: u8 = 0;
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v_fst_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1455_: u8 = 0;
    let mut v___y_1457_: u8 = 0;
    let mut v___x_11156__overap_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    let mut v___x_11158__overap_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v_isSharedCheck_1473_: u8 = 0;
    let mut v_isSharedCheck_1474_: u8 = 0;
    let mut v_data_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1482_: u8 = 0;
    let mut v_fst_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v___x_1488_: u8 = 0;
    let mut v___x_11315__overap_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut v_isSharedCheck_1499_: u8 = 0;
    let mut v_typeName_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v_fst_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1514_: u8 = 0;
    let mut v___x_11427__overap_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut v_isSharedCheck_1525_: u8 = 0;
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10529__overap_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1310_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once
                    ),
                    _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20,
                );
                v___x_1311_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30_once
                    ),
                    _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30,
                );
                v___x_1312_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
                v_share1_1313_ = lean_ctor_get(v___x_1312_, 0);
                v_assertShared_1314_ = lean_ctor_get(v___x_1312_, 1);
                v_isDebugEnabled_1315_ = lean_ctor_get(v___x_1312_, 2);
                v___x_1316_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31_once
                    ),
                    _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31,
                );
                lean_inc(v_share1_1313_);
                v___f_1317_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1317_, 0, v_share1_1313_);
                lean_closure_set(v___f_1317_, 1, v___x_1316_);
                lean_inc(v_assertShared_1314_);
                v___f_1318_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1318_, 0, v_assertShared_1314_);
                lean_closure_set(v___f_1318_, 1, v___x_1316_);
                lean_inc(v_isDebugEnabled_1315_);
                v___x_1319_ = lean_alloc_closure(l_StateT_lift as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___x_1319_, 0, lean_box(0));
                lean_closure_set(v___x_1319_, 1, lean_box(0));
                lean_closure_set(v___x_1319_, 2, v___x_1310_);
                lean_closure_set(v___x_1319_, 3, lean_box(0));
                lean_closure_set(v___x_1319_, 4, v_isDebugEnabled_1315_);
                v___x_1320_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1320_, 0, v___f_1317_);
                lean_ctor_set(v___x_1320_, 1, v___f_1318_);
                lean_ctor_set(v___x_1320_, 2, v___x_1319_);
                match lean_obj_tag(v_e_1304_) {
                    5 => {
                        v_fn_1321_ = lean_ctor_get(v_e_1304_, 0);
                        v_arg_1322_ = lean_ctor_get(v_e_1304_, 1);
                        lean_inc_ref(v_fn_1306_);
                        lean_inc(v_offset_1305_);
                        lean_inc_ref(v_fn_1321_);
                        v___x_1323_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_fn_1321_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1324_ = lean_ctor_get(v___x_1323_, 0);
                        lean_inc(v_fst_1324_);
                        v_snd_1325_ = lean_ctor_get(v___x_1323_, 1);
                        lean_inc(v_snd_1325_);
                        lean_dec_ref(v___x_1323_);
                        v_fst_1326_ = lean_ctor_get(v_fst_1324_, 0);
                        lean_inc(v_fst_1326_);
                        v_snd_1327_ = lean_ctor_get(v_fst_1324_, 1);
                        lean_inc(v_snd_1327_);
                        lean_dec(v_fst_1324_);
                        lean_inc_ref(v_arg_1322_);
                        v___x_1328_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_arg_1322_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_snd_1327_,
                                v_a_1308_,
                                v_snd_1325_,
                            );
                        v_fst_1329_ = lean_ctor_get(v___x_1328_, 0);
                        v_snd_1330_ = lean_ctor_get(v___x_1328_, 1);
                        v_isSharedCheck_1353_ = (!lean_is_exclusive(v___x_1328_)) as u8;
                        if v_isSharedCheck_1353_ == 0 {
                            v___x_1332_ = v___x_1328_;
                            v_isShared_1333_ = v_isSharedCheck_1353_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_1330_);
                            lean_inc(v_fst_1329_);
                            lean_dec(v___x_1328_);
                            v___x_1332_ = lean_box(0);
                            v_isShared_1333_ = v_isSharedCheck_1353_;
                            state = 1;
                            continue;
                        }
                    }
                    6 => {
                        v_binderName_1354_ = lean_ctor_get(v_e_1304_, 0);
                        v_binderType_1355_ = lean_ctor_get(v_e_1304_, 1);
                        v_body_1356_ = lean_ctor_get(v_e_1304_, 2);
                        v_binderInfo_1357_ = lean_ctor_get_uint8(
                            v_e_1304_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_inc_ref(v_fn_1306_);
                        lean_inc(v_offset_1305_);
                        lean_inc_ref(v_binderType_1355_);
                        v___x_1358_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_binderType_1355_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1359_ = lean_ctor_get(v___x_1358_, 0);
                        lean_inc(v_fst_1359_);
                        v_snd_1360_ = lean_ctor_get(v___x_1358_, 1);
                        lean_inc(v_snd_1360_);
                        lean_dec_ref(v___x_1358_);
                        v_fst_1361_ = lean_ctor_get(v_fst_1359_, 0);
                        lean_inc(v_fst_1361_);
                        v_snd_1362_ = lean_ctor_get(v_fst_1359_, 1);
                        lean_inc(v_snd_1362_);
                        lean_dec(v_fst_1359_);
                        v___x_1363_ = lean_unsigned_to_nat(1);
                        v___x_1364_ = lean_nat_add(v_offset_1305_, v___x_1363_);
                        lean_dec(v_offset_1305_);
                        lean_inc_ref(v_body_1356_);
                        v___x_1365_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_body_1356_,
                                v___x_1364_,
                                v_fn_1306_,
                                v_snd_1362_,
                                v_a_1308_,
                                v_snd_1360_,
                            );
                        v_fst_1366_ = lean_ctor_get(v___x_1365_, 0);
                        v_snd_1367_ = lean_ctor_get(v___x_1365_, 1);
                        v_isSharedCheck_1390_ = (!lean_is_exclusive(v___x_1365_)) as u8;
                        if v_isSharedCheck_1390_ == 0 {
                            v___x_1369_ = v___x_1365_;
                            v_isShared_1370_ = v_isSharedCheck_1390_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_snd_1367_);
                            lean_inc(v_fst_1366_);
                            lean_dec(v___x_1365_);
                            v___x_1369_ = lean_box(0);
                            v_isShared_1370_ = v_isSharedCheck_1390_;
                            state = 6;
                            continue;
                        }
                    }
                    7 => {
                        v_binderName_1391_ = lean_ctor_get(v_e_1304_, 0);
                        v_binderType_1392_ = lean_ctor_get(v_e_1304_, 1);
                        v_body_1393_ = lean_ctor_get(v_e_1304_, 2);
                        v_binderInfo_1394_ = lean_ctor_get_uint8(
                            v_e_1304_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_inc_ref(v_fn_1306_);
                        lean_inc(v_offset_1305_);
                        lean_inc_ref(v_binderType_1392_);
                        v___x_1395_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_binderType_1392_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1396_ = lean_ctor_get(v___x_1395_, 0);
                        lean_inc(v_fst_1396_);
                        v_snd_1397_ = lean_ctor_get(v___x_1395_, 1);
                        lean_inc(v_snd_1397_);
                        lean_dec_ref(v___x_1395_);
                        v_fst_1398_ = lean_ctor_get(v_fst_1396_, 0);
                        lean_inc(v_fst_1398_);
                        v_snd_1399_ = lean_ctor_get(v_fst_1396_, 1);
                        lean_inc(v_snd_1399_);
                        lean_dec(v_fst_1396_);
                        v___x_1400_ = lean_unsigned_to_nat(1);
                        v___x_1401_ = lean_nat_add(v_offset_1305_, v___x_1400_);
                        lean_dec(v_offset_1305_);
                        lean_inc_ref(v_body_1393_);
                        v___x_1402_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_body_1393_,
                                v___x_1401_,
                                v_fn_1306_,
                                v_snd_1399_,
                                v_a_1308_,
                                v_snd_1397_,
                            );
                        v_fst_1403_ = lean_ctor_get(v___x_1402_, 0);
                        v_snd_1404_ = lean_ctor_get(v___x_1402_, 1);
                        v_isSharedCheck_1427_ = (!lean_is_exclusive(v___x_1402_)) as u8;
                        if v_isSharedCheck_1427_ == 0 {
                            v___x_1406_ = v___x_1402_;
                            v_isShared_1407_ = v_isSharedCheck_1427_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_snd_1404_);
                            lean_inc(v_fst_1403_);
                            lean_dec(v___x_1402_);
                            v___x_1406_ = lean_box(0);
                            v_isShared_1407_ = v_isSharedCheck_1427_;
                            state = 11;
                            continue;
                        }
                    }
                    8 => {
                        v_declName_1428_ = lean_ctor_get(v_e_1304_, 0);
                        v_type_1429_ = lean_ctor_get(v_e_1304_, 1);
                        v_value_1430_ = lean_ctor_get(v_e_1304_, 2);
                        v_body_1431_ = lean_ctor_get(v_e_1304_, 3);
                        v_nondep_1432_ = lean_ctor_get_uint8(
                            v_e_1304_,
                            (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                        );
                        lean_inc_ref_n(v_fn_1306_, 2);
                        lean_inc_n(v_offset_1305_, 2);
                        lean_inc_ref(v_type_1429_);
                        v___x_1433_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_type_1429_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1434_ = lean_ctor_get(v___x_1433_, 0);
                        lean_inc(v_fst_1434_);
                        v_snd_1435_ = lean_ctor_get(v___x_1433_, 1);
                        lean_inc(v_snd_1435_);
                        lean_dec_ref(v___x_1433_);
                        v_fst_1436_ = lean_ctor_get(v_fst_1434_, 0);
                        lean_inc(v_fst_1436_);
                        v_snd_1437_ = lean_ctor_get(v_fst_1434_, 1);
                        lean_inc(v_snd_1437_);
                        lean_dec(v_fst_1434_);
                        lean_inc_ref(v_value_1430_);
                        v___x_1438_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_value_1430_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_snd_1437_,
                                v_a_1308_,
                                v_snd_1435_,
                            );
                        v_fst_1439_ = lean_ctor_get(v___x_1438_, 0);
                        lean_inc(v_fst_1439_);
                        v_snd_1440_ = lean_ctor_get(v___x_1438_, 1);
                        lean_inc(v_snd_1440_);
                        lean_dec_ref(v___x_1438_);
                        v_fst_1441_ = lean_ctor_get(v_fst_1439_, 0);
                        lean_inc(v_fst_1441_);
                        v_snd_1442_ = lean_ctor_get(v_fst_1439_, 1);
                        lean_inc(v_snd_1442_);
                        lean_dec(v_fst_1439_);
                        v___x_1443_ = lean_unsigned_to_nat(1);
                        v___x_1444_ = lean_nat_add(v_offset_1305_, v___x_1443_);
                        lean_dec(v_offset_1305_);
                        lean_inc_ref(v_body_1431_);
                        v___x_1445_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_body_1431_,
                                v___x_1444_,
                                v_fn_1306_,
                                v_snd_1442_,
                                v_a_1308_,
                                v_snd_1440_,
                            );
                        v_fst_1446_ = lean_ctor_get(v___x_1445_, 0);
                        v_snd_1447_ = lean_ctor_get(v___x_1445_, 1);
                        v_isSharedCheck_1474_ = (!lean_is_exclusive(v___x_1445_)) as u8;
                        if v_isSharedCheck_1474_ == 0 {
                            v___x_1449_ = v___x_1445_;
                            v_isShared_1450_ = v_isSharedCheck_1474_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_snd_1447_);
                            lean_inc(v_fst_1446_);
                            lean_dec(v___x_1445_);
                            v___x_1449_ = lean_box(0);
                            v_isShared_1450_ = v_isSharedCheck_1474_;
                            state = 16;
                            continue;
                        }
                    }
                    10 => {
                        v_data_1475_ = lean_ctor_get(v_e_1304_, 0);
                        v_expr_1476_ = lean_ctor_get(v_e_1304_, 1);
                        lean_inc_ref(v_expr_1476_);
                        v___x_1477_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_expr_1476_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1478_ = lean_ctor_get(v___x_1477_, 0);
                        v_snd_1479_ = lean_ctor_get(v___x_1477_, 1);
                        v_isSharedCheck_1499_ = (!lean_is_exclusive(v___x_1477_)) as u8;
                        if v_isSharedCheck_1499_ == 0 {
                            v___x_1481_ = v___x_1477_;
                            v_isShared_1482_ = v_isSharedCheck_1499_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_snd_1479_);
                            lean_inc(v_fst_1478_);
                            lean_dec(v___x_1477_);
                            v___x_1481_ = lean_box(0);
                            v_isShared_1482_ = v_isSharedCheck_1499_;
                            state = 21;
                            continue;
                        }
                    }
                    11 => {
                        v_typeName_1500_ = lean_ctor_get(v_e_1304_, 0);
                        v_idx_1501_ = lean_ctor_get(v_e_1304_, 1);
                        v_struct_1502_ = lean_ctor_get(v_e_1304_, 2);
                        lean_inc_ref(v_struct_1502_);
                        v___x_1503_ =
                            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(
                                v_struct_1502_,
                                v_offset_1305_,
                                v_fn_1306_,
                                v_a_1307_,
                                v_a_1308_,
                                v_a_1309_,
                            );
                        v_fst_1504_ = lean_ctor_get(v___x_1503_, 0);
                        v_snd_1505_ = lean_ctor_get(v___x_1503_, 1);
                        v_isSharedCheck_1525_ = (!lean_is_exclusive(v___x_1503_)) as u8;
                        if v_isSharedCheck_1525_ == 0 {
                            v___x_1507_ = v___x_1503_;
                            v_isShared_1508_ = v_isSharedCheck_1525_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_snd_1505_);
                            lean_inc(v_fst_1504_);
                            lean_dec(v___x_1503_);
                            v___x_1507_ = lean_box(0);
                            v_isShared_1508_ = v_isSharedCheck_1525_;
                            state = 25;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec_ref_known(v___x_1320_, 3);
                        lean_dec_ref(v_fn_1306_);
                        lean_dec(v_offset_1305_);
                        lean_dec_ref(v_e_1304_);
                        v___x_1526_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32);
                        v___x_1527_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36);
                        v___x_10529__overap_1528_ = l_panic___redArg(v___x_1526_, v___x_1527_);
                        v___x_1529_ = lean_box((v_a_1308_) as usize);
                        v___x_1530_ = lean_apply_3(
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
                v_fst_1334_ = lean_ctor_get(v_fst_1329_, 0);
                v_snd_1335_ = lean_ctor_get(v_fst_1329_, 1);
                v_isSharedCheck_1352_ = (!lean_is_exclusive(v_fst_1329_)) as u8;
                if v_isSharedCheck_1352_ == 0 {
                    v___x_1337_ = v_fst_1329_;
                    v_isShared_1338_ = v_isSharedCheck_1352_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1335_);
                    lean_inc(v_fst_1334_);
                    lean_dec(v_fst_1329_);
                    v___x_1337_ = lean_box(0);
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
                    lean_del_object(v___x_1337_);
                    lean_del_object(v___x_1332_);
                    lean_dec_ref_known(v_e_1304_, 2);
                    v___x_10643__overap_1341_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_fst_1326_,
                        v_fst_1334_,
                    );
                    v___x_1342_ = lean_box((v_a_1308_) as usize);
                    v___x_1343_ = lean_apply_3(
                        v___x_10643__overap_1341_,
                        v_snd_1335_,
                        v___x_1342_,
                        v_snd_1330_,
                    );
                    return v___x_1343_;
                } else {
                    lean_dec(v_fst_1334_);
                    lean_dec(v_fst_1326_);
                    lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1338_ == 0 {
                        lean_ctor_set(v___x_1337_, 0, v_e_1304_);
                        v___x_1345_ = v___x_1337_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_e_1304_);
                        lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_snd_1335_);
                        v___x_1345_ = v_reuseFailAlloc_1349_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1333_ == 0 {
                    lean_ctor_set(v___x_1332_, 0, v___x_1345_);
                    v___x_1347_ = v___x_1332_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
                    lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_snd_1330_);
                    v___x_1347_ = v_reuseFailAlloc_1348_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1347_;
            }
            6 => {
                v_fst_1371_ = lean_ctor_get(v_fst_1366_, 0);
                v_snd_1372_ = lean_ctor_get(v_fst_1366_, 1);
                v_isSharedCheck_1389_ = (!lean_is_exclusive(v_fst_1366_)) as u8;
                if v_isSharedCheck_1389_ == 0 {
                    v___x_1374_ = v_fst_1366_;
                    v_isShared_1375_ = v_isSharedCheck_1389_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_1372_);
                    lean_inc(v_fst_1371_);
                    lean_dec(v_fst_1366_);
                    v___x_1374_ = lean_box(0);
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
                    lean_inc(v_binderName_1354_);
                    lean_del_object(v___x_1374_);
                    lean_del_object(v___x_1369_);
                    lean_dec_ref_known(v_e_1304_, 3);
                    v___x_10804__overap_1378_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_binderName_1354_,
                        v_binderInfo_1357_,
                        v_fst_1361_,
                        v_fst_1371_,
                    );
                    v___x_1379_ = lean_box((v_a_1308_) as usize);
                    v___x_1380_ = lean_apply_3(
                        v___x_10804__overap_1378_,
                        v_snd_1372_,
                        v___x_1379_,
                        v_snd_1367_,
                    );
                    return v___x_1380_;
                } else {
                    lean_dec(v_fst_1371_);
                    lean_dec(v_fst_1361_);
                    lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1375_ == 0 {
                        lean_ctor_set(v___x_1374_, 0, v_e_1304_);
                        v___x_1382_ = v___x_1374_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_e_1304_);
                        lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_snd_1372_);
                        v___x_1382_ = v_reuseFailAlloc_1386_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1370_ == 0 {
                    lean_ctor_set(v___x_1369_, 0, v___x_1382_);
                    v___x_1384_ = v___x_1369_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
                    lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_snd_1367_);
                    v___x_1384_ = v_reuseFailAlloc_1385_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1384_;
            }
            11 => {
                v_fst_1408_ = lean_ctor_get(v_fst_1403_, 0);
                v_snd_1409_ = lean_ctor_get(v_fst_1403_, 1);
                v_isSharedCheck_1426_ = (!lean_is_exclusive(v_fst_1403_)) as u8;
                if v_isSharedCheck_1426_ == 0 {
                    v___x_1411_ = v_fst_1403_;
                    v_isShared_1412_ = v_isSharedCheck_1426_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_1409_);
                    lean_inc(v_fst_1408_);
                    lean_dec(v_fst_1403_);
                    v___x_1411_ = lean_box(0);
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
                    lean_inc(v_binderName_1391_);
                    lean_del_object(v___x_1411_);
                    lean_del_object(v___x_1406_);
                    lean_dec_ref_known(v_e_1304_, 3);
                    v___x_10969__overap_1415_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_binderName_1391_,
                        v_binderInfo_1394_,
                        v_fst_1398_,
                        v_fst_1408_,
                    );
                    v___x_1416_ = lean_box((v_a_1308_) as usize);
                    v___x_1417_ = lean_apply_3(
                        v___x_10969__overap_1415_,
                        v_snd_1409_,
                        v___x_1416_,
                        v_snd_1404_,
                    );
                    return v___x_1417_;
                } else {
                    lean_dec(v_fst_1408_);
                    lean_dec(v_fst_1398_);
                    lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1412_ == 0 {
                        lean_ctor_set(v___x_1411_, 0, v_e_1304_);
                        v___x_1419_ = v___x_1411_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_e_1304_);
                        lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_snd_1409_);
                        v___x_1419_ = v_reuseFailAlloc_1423_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_1407_ == 0 {
                    lean_ctor_set(v___x_1406_, 0, v___x_1419_);
                    v___x_1421_ = v___x_1406_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_snd_1404_);
                    v___x_1421_ = v_reuseFailAlloc_1422_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1421_;
            }
            16 => {
                v_fst_1451_ = lean_ctor_get(v_fst_1446_, 0);
                v_snd_1452_ = lean_ctor_get(v_fst_1446_, 1);
                v_isSharedCheck_1473_ = (!lean_is_exclusive(v_fst_1446_)) as u8;
                if v_isSharedCheck_1473_ == 0 {
                    v___x_1454_ = v_fst_1446_;
                    v_isShared_1455_ = v_isSharedCheck_1473_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_snd_1452_);
                    lean_inc(v_fst_1451_);
                    lean_dec(v_fst_1446_);
                    v___x_1454_ = lean_box(0);
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
                    lean_inc(v_declName_1428_);
                    lean_del_object(v___x_1454_);
                    lean_del_object(v___x_1449_);
                    lean_dec_ref_known(v_e_1304_, 4);
                    v___x_11156__overap_1458_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_declName_1428_,
                        v_fst_1436_,
                        v_fst_1441_,
                        v_fst_1451_,
                        v_nondep_1432_,
                    );
                    v___x_1459_ = lean_box((v_a_1308_) as usize);
                    v___x_1460_ = lean_apply_3(
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
                        lean_inc(v_declName_1428_);
                        lean_del_object(v___x_1454_);
                        lean_del_object(v___x_1449_);
                        lean_dec_ref_known(v_e_1304_, 4);
                        v___x_11158__overap_1462_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
                            v___x_1320_,
                            v___x_1311_,
                            v_declName_1428_,
                            v_fst_1436_,
                            v_fst_1441_,
                            v_fst_1451_,
                            v_nondep_1432_,
                        );
                        v___x_1463_ = lean_box((v_a_1308_) as usize);
                        v___x_1464_ = lean_apply_3(
                            v___x_11158__overap_1462_,
                            v_snd_1452_,
                            v___x_1463_,
                            v_snd_1447_,
                        );
                        return v___x_1464_;
                    } else {
                        lean_dec(v_fst_1451_);
                        lean_dec(v_fst_1441_);
                        lean_dec(v_fst_1436_);
                        lean_dec_ref_known(v___x_1320_, 3);
                        if v_isShared_1455_ == 0 {
                            lean_ctor_set(v___x_1454_, 0, v_e_1304_);
                            v___x_1466_ = v___x_1454_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_e_1304_);
                            lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_snd_1452_);
                            v___x_1466_ = v_reuseFailAlloc_1470_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_1450_ == 0 {
                    lean_ctor_set(v___x_1449_, 0, v___x_1466_);
                    v___x_1468_ = v___x_1449_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
                    lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_snd_1447_);
                    v___x_1468_ = v_reuseFailAlloc_1469_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1468_;
            }
            21 => {
                v_fst_1483_ = lean_ctor_get(v_fst_1478_, 0);
                v_snd_1484_ = lean_ctor_get(v_fst_1478_, 1);
                v_isSharedCheck_1498_ = (!lean_is_exclusive(v_fst_1478_)) as u8;
                if v_isSharedCheck_1498_ == 0 {
                    v___x_1486_ = v_fst_1478_;
                    v_isShared_1487_ = v_isSharedCheck_1498_;
                    state = 22;
                    continue;
                } else {
                    lean_inc(v_snd_1484_);
                    lean_inc(v_fst_1483_);
                    lean_dec(v_fst_1478_);
                    v___x_1486_ = lean_box(0);
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
                    lean_inc(v_data_1475_);
                    lean_del_object(v___x_1486_);
                    lean_del_object(v___x_1481_);
                    lean_dec_ref_known(v_e_1304_, 2);
                    v___x_11315__overap_1489_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_data_1475_,
                        v_fst_1483_,
                    );
                    v___x_1490_ = lean_box((v_a_1308_) as usize);
                    v___x_1491_ = lean_apply_3(
                        v___x_11315__overap_1489_,
                        v_snd_1484_,
                        v___x_1490_,
                        v_snd_1479_,
                    );
                    return v___x_1491_;
                } else {
                    lean_dec(v_fst_1483_);
                    lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1487_ == 0 {
                        lean_ctor_set(v___x_1486_, 0, v_e_1304_);
                        v___x_1493_ = v___x_1486_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_e_1304_);
                        lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_snd_1484_);
                        v___x_1493_ = v_reuseFailAlloc_1497_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1482_ == 0 {
                    lean_ctor_set(v___x_1481_, 0, v___x_1493_);
                    v___x_1495_ = v___x_1481_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
                    lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_snd_1479_);
                    v___x_1495_ = v_reuseFailAlloc_1496_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1495_;
            }
            25 => {
                v_fst_1509_ = lean_ctor_get(v_fst_1504_, 0);
                v_snd_1510_ = lean_ctor_get(v_fst_1504_, 1);
                v_isSharedCheck_1524_ = (!lean_is_exclusive(v_fst_1504_)) as u8;
                if v_isSharedCheck_1524_ == 0 {
                    v___x_1512_ = v_fst_1504_;
                    v_isShared_1513_ = v_isSharedCheck_1524_;
                    state = 26;
                    continue;
                } else {
                    lean_inc(v_snd_1510_);
                    lean_inc(v_fst_1509_);
                    lean_dec(v_fst_1504_);
                    v___x_1512_ = lean_box(0);
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
                    lean_inc(v_idx_1501_);
                    lean_inc(v_typeName_1500_);
                    lean_del_object(v___x_1512_);
                    lean_del_object(v___x_1507_);
                    lean_dec_ref_known(v_e_1304_, 3);
                    v___x_11427__overap_1515_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(
                        v___x_1320_,
                        v___x_1311_,
                        v_typeName_1500_,
                        v_idx_1501_,
                        v_fst_1509_,
                    );
                    v___x_1516_ = lean_box((v_a_1308_) as usize);
                    v___x_1517_ = lean_apply_3(
                        v___x_11427__overap_1515_,
                        v_snd_1510_,
                        v___x_1516_,
                        v_snd_1505_,
                    );
                    return v___x_1517_;
                } else {
                    lean_dec(v_fst_1509_);
                    lean_dec_ref_known(v___x_1320_, 3);
                    if v_isShared_1513_ == 0 {
                        lean_ctor_set(v___x_1512_, 0, v_e_1304_);
                        v___x_1519_ = v___x_1512_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_e_1304_);
                        lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_snd_1510_);
                        v___x_1519_ = v_reuseFailAlloc_1523_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_1508_ == 0 {
                    lean_ctor_set(v___x_1507_, 0, v___x_1519_);
                    v___x_1521_ = v___x_1507_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
                    lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_snd_1505_);
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
    mut v_e_1531_: *mut LeanObject,
    mut v_offset_1532_: *mut LeanObject,
    mut v_f_1533_: *mut LeanObject,
    mut v_a_1534_: *mut LeanObject,
    mut v_a_1535_: u8,
    mut v_a_1536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    v___f_1537_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3;
    lean_inc(v_offset_1532_);
    lean_inc_ref(v_e_1531_);
    v_key_1538_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_key_1538_, 0, v_e_1531_);
    lean_ctor_set(v_key_1538_, 1, v_offset_1532_);
    v___f_1539_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once
        ),
        _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5,
    );
    lean_inc_ref(v_key_1538_);
    v___x_1540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_1539_,
        v___f_1537_,
        v_a_1534_,
        v_key_1538_,
    );
    if lean_obj_tag(v___x_1540_) == 1 {
        let mut v_val_1541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_key_1538_, 2);
        lean_dec_ref(v_f_1533_);
        lean_dec(v_offset_1532_);
        lean_dec_ref(v_e_1531_);
        v_val_1541_ = lean_ctor_get(v___x_1540_, 0);
        lean_inc(v_val_1541_);
        lean_dec_ref_known(v___x_1540_, 1);
        v___x_1542_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1542_, 0, v_val_1541_);
        lean_ctor_set(v___x_1542_, 1, v_a_1534_);
        v___x_1543_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1543_, 0, v___x_1542_);
        lean_ctor_set(v___x_1543_, 1, v_a_1536_);
        return v___x_1543_;
    } else {
        let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1546_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1540_);
        v___x_1544_ = lean_box((v_a_1535_) as usize);
        lean_inc_ref(v_f_1533_);
        lean_inc(v_offset_1532_);
        lean_inc_ref(v_e_1531_);
        v___x_1545_ = lean_apply_4(v_f_1533_, v_e_1531_, v_offset_1532_, v___x_1544_, v_a_1536_);
        v_fst_1546_ = lean_ctor_get(v___x_1545_, 0);
        lean_inc(v_fst_1546_);
        if lean_obj_tag(v_fst_1546_) == 1 {
            let mut v_snd_1547_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1548_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_f_1533_);
            lean_dec(v_offset_1532_);
            lean_dec_ref(v_e_1531_);
            v_snd_1547_ = lean_ctor_get(v___x_1545_, 1);
            lean_inc(v_snd_1547_);
            lean_dec_ref(v___x_1545_);
            v_val_1548_ = lean_ctor_get(v_fst_1546_, 0);
            lean_inc(v_val_1548_);
            lean_dec_ref_known(v_fst_1546_, 1);
            v___x_1549_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                v_key_1538_,
                v_val_1548_,
                v_a_1534_,
                v_snd_1547_,
            );
            return v___x_1549_;
        } else {
            lean_dec(v_fst_1546_);
            match lean_obj_tag(v_e_1531_) {
                9 => {
                    let mut v_snd_1550_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_f_1533_);
                    lean_dec(v_offset_1532_);
                    v_snd_1550_ = lean_ctor_get(v___x_1545_, 1);
                    lean_inc(v_snd_1550_);
                    lean_dec_ref(v___x_1545_);
                    v___x_1551_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1550_,
                    );
                    return v___x_1551_;
                }
                2 => {
                    let mut v_snd_1552_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_f_1533_);
                    lean_dec(v_offset_1532_);
                    v_snd_1552_ = lean_ctor_get(v___x_1545_, 1);
                    lean_inc(v_snd_1552_);
                    lean_dec_ref(v___x_1545_);
                    v___x_1553_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1552_,
                    );
                    return v___x_1553_;
                }
                0 => {
                    let mut v_snd_1554_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_f_1533_);
                    lean_dec(v_offset_1532_);
                    v_snd_1554_ = lean_ctor_get(v___x_1545_, 1);
                    lean_inc(v_snd_1554_);
                    lean_dec_ref(v___x_1545_);
                    v___x_1555_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1554_,
                    );
                    return v___x_1555_;
                }
                1 => {
                    let mut v_snd_1556_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_f_1533_);
                    lean_dec(v_offset_1532_);
                    v_snd_1556_ = lean_ctor_get(v___x_1545_, 1);
                    lean_inc(v_snd_1556_);
                    lean_dec_ref(v___x_1545_);
                    v___x_1557_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1556_,
                    );
                    return v___x_1557_;
                }
                4 => {
                    let mut v_snd_1558_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_f_1533_);
                    lean_dec(v_offset_1532_);
                    v_snd_1558_ = lean_ctor_get(v___x_1545_, 1);
                    lean_inc(v_snd_1558_);
                    lean_dec_ref(v___x_1545_);
                    v___x_1559_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1558_,
                    );
                    return v___x_1559_;
                }
                3 => {
                    let mut v_snd_1560_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_f_1533_);
                    lean_dec(v_offset_1532_);
                    v_snd_1560_ = lean_ctor_get(v___x_1545_, 1);
                    lean_inc(v_snd_1560_);
                    lean_dec_ref(v___x_1545_);
                    v___x_1561_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(
                        v_key_1538_,
                        v_e_1531_,
                        v_a_1534_,
                        v_snd_1560_,
                    );
                    return v___x_1561_;
                }
                _ => {
                    let mut v_snd_1562_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_fst_1564_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_snd_1565_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_fst_1566_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_snd_1567_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
                    v_snd_1562_ = lean_ctor_get(v___x_1545_, 1);
                    lean_inc(v_snd_1562_);
                    lean_dec_ref(v___x_1545_);
                    v___x_1563_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(
                        v_e_1531_,
                        v_offset_1532_,
                        v_f_1533_,
                        v_a_1534_,
                        v_a_1535_,
                        v_snd_1562_,
                    );
                    v_fst_1564_ = lean_ctor_get(v___x_1563_, 0);
                    lean_inc(v_fst_1564_);
                    v_snd_1565_ = lean_ctor_get(v___x_1563_, 1);
                    lean_inc(v_snd_1565_);
                    lean_dec_ref(v___x_1563_);
                    v_fst_1566_ = lean_ctor_get(v_fst_1564_, 0);
                    lean_inc(v_fst_1566_);
                    v_snd_1567_ = lean_ctor_get(v_fst_1564_, 1);
                    lean_inc(v_snd_1567_);
                    lean_dec(v_fst_1564_);
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
    mut v_e_1569_: *mut LeanObject,
    mut v_offset_1570_: *mut LeanObject,
    mut v_f_1571_: *mut LeanObject,
    mut v_a_1572_: *mut LeanObject,
    mut v_a_1573_: *mut LeanObject,
    mut v_a_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1575_: u8 = 0;
    let mut v_res_1576_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1575_ = (lean_unbox(v_a_1573_) as u8);
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
    mut v_e_1577_: *mut LeanObject,
    mut v_offset_1578_: *mut LeanObject,
    mut v_fn_1579_: *mut LeanObject,
    mut v_a_1580_: *mut LeanObject,
    mut v_a_1581_: *mut LeanObject,
    mut v_a_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1583_: u8 = 0;
    let mut v_res_1584_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1583_ = (lean_unbox(v_a_1581_) as u8);
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
    mut v_____do__lift_1585_: *mut LeanObject,
    mut v_h__1_1586_: *mut LeanObject,
    mut v_h__2_1587_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1585_) == 1 {
        let mut v_val_1588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1587_);
        v_val_1588_ = lean_ctor_get(v_____do__lift_1585_, 0);
        lean_inc(v_val_1588_);
        lean_dec_ref_known(v_____do__lift_1585_, 1);
        v___x_1589_ = lean_apply_1(v_h__1_1586_, v_val_1588_);
        return v___x_1589_;
    } else {
        let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1586_);
        v___x_1590_ = lean_apply_2(v_h__2_1587_, v_____do__lift_1585_, lean_box(0));
        return v___x_1590_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(
    mut v_motive_1591_: *mut LeanObject,
    mut v_____do__lift_1592_: *mut LeanObject,
    mut v_h__1_1593_: *mut LeanObject,
    mut v_h__2_1594_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1592_) == 1 {
        let mut v_val_1595_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1594_);
        v_val_1595_ = lean_ctor_get(v_____do__lift_1592_, 0);
        lean_inc(v_val_1595_);
        lean_dec_ref_known(v_____do__lift_1592_, 1);
        v___x_1596_ = lean_apply_1(v_h__1_1593_, v_val_1595_);
        return v___x_1596_;
    } else {
        let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1593_);
        v___x_1597_ = lean_apply_2(v_h__2_1594_, v_____do__lift_1592_, lean_box(0));
        return v___x_1597_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(
    mut v_e_1598_: *mut LeanObject,
    mut v_h__1_1599_: *mut LeanObject,
    mut v_h__2_1600_: *mut LeanObject,
    mut v_h__3_1601_: *mut LeanObject,
    mut v_h__4_1602_: *mut LeanObject,
    mut v_h__5_1603_: *mut LeanObject,
    mut v_h__6_1604_: *mut LeanObject,
    mut v_h__7_1605_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_e_1598_) {
        9 => {
            let mut v_a_1606_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1605_);
            lean_dec(v_h__6_1604_);
            lean_dec(v_h__5_1603_);
            lean_dec(v_h__4_1602_);
            lean_dec(v_h__3_1601_);
            lean_dec(v_h__2_1600_);
            v_a_1606_ = lean_ctor_get(v_e_1598_, 0);
            lean_inc_ref(v_a_1606_);
            lean_dec_ref_known(v_e_1598_, 1);
            v___x_1607_ = lean_apply_1(v_h__1_1599_, v_a_1606_);
            return v___x_1607_;
        }
        2 => {
            let mut v_mvarId_1608_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1605_);
            lean_dec(v_h__6_1604_);
            lean_dec(v_h__5_1603_);
            lean_dec(v_h__4_1602_);
            lean_dec(v_h__3_1601_);
            lean_dec(v_h__1_1599_);
            v_mvarId_1608_ = lean_ctor_get(v_e_1598_, 0);
            lean_inc(v_mvarId_1608_);
            lean_dec_ref_known(v_e_1598_, 1);
            v___x_1609_ = lean_apply_1(v_h__2_1600_, v_mvarId_1608_);
            return v___x_1609_;
        }
        0 => {
            let mut v_deBruijnIndex_1610_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1605_);
            lean_dec(v_h__6_1604_);
            lean_dec(v_h__5_1603_);
            lean_dec(v_h__4_1602_);
            lean_dec(v_h__2_1600_);
            lean_dec(v_h__1_1599_);
            v_deBruijnIndex_1610_ = lean_ctor_get(v_e_1598_, 0);
            lean_inc(v_deBruijnIndex_1610_);
            lean_dec_ref_known(v_e_1598_, 1);
            v___x_1611_ = lean_apply_1(v_h__3_1601_, v_deBruijnIndex_1610_);
            return v___x_1611_;
        }
        1 => {
            let mut v_fvarId_1612_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1605_);
            lean_dec(v_h__6_1604_);
            lean_dec(v_h__5_1603_);
            lean_dec(v_h__3_1601_);
            lean_dec(v_h__2_1600_);
            lean_dec(v_h__1_1599_);
            v_fvarId_1612_ = lean_ctor_get(v_e_1598_, 0);
            lean_inc(v_fvarId_1612_);
            lean_dec_ref_known(v_e_1598_, 1);
            v___x_1613_ = lean_apply_1(v_h__4_1602_, v_fvarId_1612_);
            return v___x_1613_;
        }
        4 => {
            let mut v_declName_1614_: *mut LeanObject = core::ptr::null_mut();
            let mut v_us_1615_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1605_);
            lean_dec(v_h__6_1604_);
            lean_dec(v_h__4_1602_);
            lean_dec(v_h__3_1601_);
            lean_dec(v_h__2_1600_);
            lean_dec(v_h__1_1599_);
            v_declName_1614_ = lean_ctor_get(v_e_1598_, 0);
            lean_inc(v_declName_1614_);
            v_us_1615_ = lean_ctor_get(v_e_1598_, 1);
            lean_inc(v_us_1615_);
            lean_dec_ref_known(v_e_1598_, 2);
            v___x_1616_ = lean_apply_2(v_h__5_1603_, v_declName_1614_, v_us_1615_);
            return v___x_1616_;
        }
        3 => {
            let mut v_u_1617_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1605_);
            lean_dec(v_h__5_1603_);
            lean_dec(v_h__4_1602_);
            lean_dec(v_h__3_1601_);
            lean_dec(v_h__2_1600_);
            lean_dec(v_h__1_1599_);
            v_u_1617_ = lean_ctor_get(v_e_1598_, 0);
            lean_inc(v_u_1617_);
            lean_dec_ref_known(v_e_1598_, 1);
            v___x_1618_ = lean_apply_1(v_h__6_1604_, v_u_1617_);
            return v___x_1618_;
        }
        _ => {
            let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_1604_);
            lean_dec(v_h__5_1603_);
            lean_dec(v_h__4_1602_);
            lean_dec(v_h__3_1601_);
            lean_dec(v_h__2_1600_);
            lean_dec(v_h__1_1599_);
            v___x_1619_ = lean_apply_7(
                v_h__7_1605_,
                v_e_1598_,
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
            );
            return v___x_1619_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(
    mut v_motive_1620_: *mut LeanObject,
    mut v_e_1621_: *mut LeanObject,
    mut v_h__1_1622_: *mut LeanObject,
    mut v_h__2_1623_: *mut LeanObject,
    mut v_h__3_1624_: *mut LeanObject,
    mut v_h__4_1625_: *mut LeanObject,
    mut v_h__5_1626_: *mut LeanObject,
    mut v_h__6_1627_: *mut LeanObject,
    mut v_h__7_1628_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_e_1621_) {
        9 => {
            let mut v_a_1629_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1628_);
            lean_dec(v_h__6_1627_);
            lean_dec(v_h__5_1626_);
            lean_dec(v_h__4_1625_);
            lean_dec(v_h__3_1624_);
            lean_dec(v_h__2_1623_);
            v_a_1629_ = lean_ctor_get(v_e_1621_, 0);
            lean_inc_ref(v_a_1629_);
            lean_dec_ref_known(v_e_1621_, 1);
            v___x_1630_ = lean_apply_1(v_h__1_1622_, v_a_1629_);
            return v___x_1630_;
        }
        2 => {
            let mut v_mvarId_1631_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1628_);
            lean_dec(v_h__6_1627_);
            lean_dec(v_h__5_1626_);
            lean_dec(v_h__4_1625_);
            lean_dec(v_h__3_1624_);
            lean_dec(v_h__1_1622_);
            v_mvarId_1631_ = lean_ctor_get(v_e_1621_, 0);
            lean_inc(v_mvarId_1631_);
            lean_dec_ref_known(v_e_1621_, 1);
            v___x_1632_ = lean_apply_1(v_h__2_1623_, v_mvarId_1631_);
            return v___x_1632_;
        }
        0 => {
            let mut v_deBruijnIndex_1633_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1628_);
            lean_dec(v_h__6_1627_);
            lean_dec(v_h__5_1626_);
            lean_dec(v_h__4_1625_);
            lean_dec(v_h__2_1623_);
            lean_dec(v_h__1_1622_);
            v_deBruijnIndex_1633_ = lean_ctor_get(v_e_1621_, 0);
            lean_inc(v_deBruijnIndex_1633_);
            lean_dec_ref_known(v_e_1621_, 1);
            v___x_1634_ = lean_apply_1(v_h__3_1624_, v_deBruijnIndex_1633_);
            return v___x_1634_;
        }
        1 => {
            let mut v_fvarId_1635_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1628_);
            lean_dec(v_h__6_1627_);
            lean_dec(v_h__5_1626_);
            lean_dec(v_h__3_1624_);
            lean_dec(v_h__2_1623_);
            lean_dec(v_h__1_1622_);
            v_fvarId_1635_ = lean_ctor_get(v_e_1621_, 0);
            lean_inc(v_fvarId_1635_);
            lean_dec_ref_known(v_e_1621_, 1);
            v___x_1636_ = lean_apply_1(v_h__4_1625_, v_fvarId_1635_);
            return v___x_1636_;
        }
        4 => {
            let mut v_declName_1637_: *mut LeanObject = core::ptr::null_mut();
            let mut v_us_1638_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1628_);
            lean_dec(v_h__6_1627_);
            lean_dec(v_h__4_1625_);
            lean_dec(v_h__3_1624_);
            lean_dec(v_h__2_1623_);
            lean_dec(v_h__1_1622_);
            v_declName_1637_ = lean_ctor_get(v_e_1621_, 0);
            lean_inc(v_declName_1637_);
            v_us_1638_ = lean_ctor_get(v_e_1621_, 1);
            lean_inc(v_us_1638_);
            lean_dec_ref_known(v_e_1621_, 2);
            v___x_1639_ = lean_apply_2(v_h__5_1626_, v_declName_1637_, v_us_1638_);
            return v___x_1639_;
        }
        3 => {
            let mut v_u_1640_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1628_);
            lean_dec(v_h__5_1626_);
            lean_dec(v_h__4_1625_);
            lean_dec(v_h__3_1624_);
            lean_dec(v_h__2_1623_);
            lean_dec(v_h__1_1622_);
            v_u_1640_ = lean_ctor_get(v_e_1621_, 0);
            lean_inc(v_u_1640_);
            lean_dec_ref_known(v_e_1621_, 1);
            v___x_1641_ = lean_apply_1(v_h__6_1627_, v_u_1640_);
            return v___x_1641_;
        }
        _ => {
            let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_1627_);
            lean_dec(v_h__5_1626_);
            lean_dec(v_h__4_1625_);
            lean_dec(v_h__3_1624_);
            lean_dec(v_h__2_1623_);
            lean_dec(v_h__1_1622_);
            v___x_1642_ = lean_apply_7(
                v_h__7_1628_,
                v_e_1621_,
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
            );
            return v___x_1642_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(
    mut v_e_1643_: *mut LeanObject,
    mut v_h__1_1644_: *mut LeanObject,
    mut v_h__2_1645_: *mut LeanObject,
    mut v_h__3_1646_: *mut LeanObject,
    mut v_h__4_1647_: *mut LeanObject,
    mut v_h__5_1648_: *mut LeanObject,
    mut v_h__6_1649_: *mut LeanObject,
    mut v_h__7_1650_: *mut LeanObject,
    mut v_h__8_1651_: *mut LeanObject,
    mut v_h__9_1652_: *mut LeanObject,
    mut v_h__10_1653_: *mut LeanObject,
    mut v_h__11_1654_: *mut LeanObject,
    mut v_h__12_1655_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_e_1643_) {
        0 => {
            let mut v_deBruijnIndex_1656_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_deBruijnIndex_1656_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_deBruijnIndex_1656_);
            lean_dec_ref_known(v_e_1643_, 1);
            v___x_1657_ = lean_apply_1(v_h__3_1646_, v_deBruijnIndex_1656_);
            return v___x_1657_;
        }
        1 => {
            let mut v_fvarId_1658_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_fvarId_1658_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_fvarId_1658_);
            lean_dec_ref_known(v_e_1643_, 1);
            v___x_1659_ = lean_apply_1(v_h__4_1647_, v_fvarId_1658_);
            return v___x_1659_;
        }
        2 => {
            let mut v_mvarId_1660_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__1_1644_);
            v_mvarId_1660_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_mvarId_1660_);
            lean_dec_ref_known(v_e_1643_, 1);
            v___x_1661_ = lean_apply_1(v_h__2_1645_, v_mvarId_1660_);
            return v___x_1661_;
        }
        3 => {
            let mut v_u_1662_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_u_1662_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_u_1662_);
            lean_dec_ref_known(v_e_1643_, 1);
            v___x_1663_ = lean_apply_1(v_h__6_1649_, v_u_1662_);
            return v___x_1663_;
        }
        4 => {
            let mut v_declName_1664_: *mut LeanObject = core::ptr::null_mut();
            let mut v_us_1665_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_declName_1664_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_declName_1664_);
            v_us_1665_ = lean_ctor_get(v_e_1643_, 1);
            lean_inc(v_us_1665_);
            lean_dec_ref_known(v_e_1643_, 2);
            v___x_1666_ = lean_apply_2(v_h__5_1648_, v_declName_1664_, v_us_1665_);
            return v___x_1666_;
        }
        5 => {
            let mut v_fn_1667_: *mut LeanObject = core::ptr::null_mut();
            let mut v_arg_1668_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_fn_1667_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc_ref(v_fn_1667_);
            v_arg_1668_ = lean_ctor_get(v_e_1643_, 1);
            lean_inc_ref(v_arg_1668_);
            lean_dec_ref_known(v_e_1643_, 2);
            v___x_1669_ = lean_apply_2(v_h__7_1650_, v_fn_1667_, v_arg_1668_);
            return v___x_1669_;
        }
        6 => {
            let mut v_binderName_1670_: *mut LeanObject = core::ptr::null_mut();
            let mut v_binderType_1671_: *mut LeanObject = core::ptr::null_mut();
            let mut v_body_1672_: *mut LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1673_: u8 = 0;
            let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_binderName_1670_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_binderName_1670_);
            v_binderType_1671_ = lean_ctor_get(v_e_1643_, 1);
            lean_inc_ref(v_binderType_1671_);
            v_body_1672_ = lean_ctor_get(v_e_1643_, 2);
            lean_inc_ref(v_body_1672_);
            v_binderInfo_1673_ = lean_ctor_get_uint8(
                v_e_1643_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
            );
            lean_dec_ref_known(v_e_1643_, 3);
            v___x_1674_ = lean_box((v_binderInfo_1673_) as usize);
            v___x_1675_ = lean_apply_4(
                v_h__11_1654_,
                v_binderName_1670_,
                v_binderType_1671_,
                v_body_1672_,
                v___x_1674_,
            );
            return v___x_1675_;
        }
        7 => {
            let mut v_binderName_1676_: *mut LeanObject = core::ptr::null_mut();
            let mut v_binderType_1677_: *mut LeanObject = core::ptr::null_mut();
            let mut v_body_1678_: *mut LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1679_: u8 = 0;
            let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_binderName_1676_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_binderName_1676_);
            v_binderType_1677_ = lean_ctor_get(v_e_1643_, 1);
            lean_inc_ref(v_binderType_1677_);
            v_body_1678_ = lean_ctor_get(v_e_1643_, 2);
            lean_inc_ref(v_body_1678_);
            v_binderInfo_1679_ = lean_ctor_get_uint8(
                v_e_1643_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
            );
            lean_dec_ref_known(v_e_1643_, 3);
            v___x_1680_ = lean_box((v_binderInfo_1679_) as usize);
            v___x_1681_ = lean_apply_4(
                v_h__10_1653_,
                v_binderName_1676_,
                v_binderType_1677_,
                v_body_1678_,
                v___x_1680_,
            );
            return v___x_1681_;
        }
        8 => {
            let mut v_declName_1682_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_1683_: *mut LeanObject = core::ptr::null_mut();
            let mut v_value_1684_: *mut LeanObject = core::ptr::null_mut();
            let mut v_body_1685_: *mut LeanObject = core::ptr::null_mut();
            let mut v_nondep_1686_: u8 = 0;
            let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_declName_1682_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_declName_1682_);
            v_type_1683_ = lean_ctor_get(v_e_1643_, 1);
            lean_inc_ref(v_type_1683_);
            v_value_1684_ = lean_ctor_get(v_e_1643_, 2);
            lean_inc_ref(v_value_1684_);
            v_body_1685_ = lean_ctor_get(v_e_1643_, 3);
            lean_inc_ref(v_body_1685_);
            v_nondep_1686_ = lean_ctor_get_uint8(
                v_e_1643_,
                (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
            );
            lean_dec_ref_known(v_e_1643_, 4);
            v___x_1687_ = lean_box((v_nondep_1686_) as usize);
            v___x_1688_ = lean_apply_5(
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
            let mut v_a_1689_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            v_a_1689_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc_ref(v_a_1689_);
            lean_dec_ref_known(v_e_1643_, 1);
            v___x_1690_ = lean_apply_1(v_h__1_1644_, v_a_1689_);
            return v___x_1690_;
        }
        10 => {
            let mut v_data_1691_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expr_1692_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__9_1652_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_data_1691_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_data_1691_);
            v_expr_1692_ = lean_ctor_get(v_e_1643_, 1);
            lean_inc_ref(v_expr_1692_);
            lean_dec_ref_known(v_e_1643_, 2);
            v___x_1693_ = lean_apply_2(v_h__8_1651_, v_data_1691_, v_expr_1692_);
            return v___x_1693_;
        }
        _ => {
            let mut v_typeName_1694_: *mut LeanObject = core::ptr::null_mut();
            let mut v_idx_1695_: *mut LeanObject = core::ptr::null_mut();
            let mut v_struct_1696_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1655_);
            lean_dec(v_h__11_1654_);
            lean_dec(v_h__10_1653_);
            lean_dec(v_h__8_1651_);
            lean_dec(v_h__7_1650_);
            lean_dec(v_h__6_1649_);
            lean_dec(v_h__5_1648_);
            lean_dec(v_h__4_1647_);
            lean_dec(v_h__3_1646_);
            lean_dec(v_h__2_1645_);
            lean_dec(v_h__1_1644_);
            v_typeName_1694_ = lean_ctor_get(v_e_1643_, 0);
            lean_inc(v_typeName_1694_);
            v_idx_1695_ = lean_ctor_get(v_e_1643_, 1);
            lean_inc(v_idx_1695_);
            v_struct_1696_ = lean_ctor_get(v_e_1643_, 2);
            lean_inc_ref(v_struct_1696_);
            lean_dec_ref_known(v_e_1643_, 3);
            v___x_1697_ = lean_apply_3(v_h__9_1652_, v_typeName_1694_, v_idx_1695_, v_struct_1696_);
            return v___x_1697_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(
    mut v_motive_1698_: *mut LeanObject,
    mut v_e_1699_: *mut LeanObject,
    mut v_h__1_1700_: *mut LeanObject,
    mut v_h__2_1701_: *mut LeanObject,
    mut v_h__3_1702_: *mut LeanObject,
    mut v_h__4_1703_: *mut LeanObject,
    mut v_h__5_1704_: *mut LeanObject,
    mut v_h__6_1705_: *mut LeanObject,
    mut v_h__7_1706_: *mut LeanObject,
    mut v_h__8_1707_: *mut LeanObject,
    mut v_h__9_1708_: *mut LeanObject,
    mut v_h__10_1709_: *mut LeanObject,
    mut v_h__11_1710_: *mut LeanObject,
    mut v_h__12_1711_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_e_1699_) {
        0 => {
            let mut v_deBruijnIndex_1712_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_deBruijnIndex_1712_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_deBruijnIndex_1712_);
            lean_dec_ref_known(v_e_1699_, 1);
            v___x_1713_ = lean_apply_1(v_h__3_1702_, v_deBruijnIndex_1712_);
            return v___x_1713_;
        }
        1 => {
            let mut v_fvarId_1714_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_fvarId_1714_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_fvarId_1714_);
            lean_dec_ref_known(v_e_1699_, 1);
            v___x_1715_ = lean_apply_1(v_h__4_1703_, v_fvarId_1714_);
            return v___x_1715_;
        }
        2 => {
            let mut v_mvarId_1716_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__1_1700_);
            v_mvarId_1716_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_mvarId_1716_);
            lean_dec_ref_known(v_e_1699_, 1);
            v___x_1717_ = lean_apply_1(v_h__2_1701_, v_mvarId_1716_);
            return v___x_1717_;
        }
        3 => {
            let mut v_u_1718_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_u_1718_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_u_1718_);
            lean_dec_ref_known(v_e_1699_, 1);
            v___x_1719_ = lean_apply_1(v_h__6_1705_, v_u_1718_);
            return v___x_1719_;
        }
        4 => {
            let mut v_declName_1720_: *mut LeanObject = core::ptr::null_mut();
            let mut v_us_1721_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_declName_1720_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_declName_1720_);
            v_us_1721_ = lean_ctor_get(v_e_1699_, 1);
            lean_inc(v_us_1721_);
            lean_dec_ref_known(v_e_1699_, 2);
            v___x_1722_ = lean_apply_2(v_h__5_1704_, v_declName_1720_, v_us_1721_);
            return v___x_1722_;
        }
        5 => {
            let mut v_fn_1723_: *mut LeanObject = core::ptr::null_mut();
            let mut v_arg_1724_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_fn_1723_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc_ref(v_fn_1723_);
            v_arg_1724_ = lean_ctor_get(v_e_1699_, 1);
            lean_inc_ref(v_arg_1724_);
            lean_dec_ref_known(v_e_1699_, 2);
            v___x_1725_ = lean_apply_2(v_h__7_1706_, v_fn_1723_, v_arg_1724_);
            return v___x_1725_;
        }
        6 => {
            let mut v_binderName_1726_: *mut LeanObject = core::ptr::null_mut();
            let mut v_binderType_1727_: *mut LeanObject = core::ptr::null_mut();
            let mut v_body_1728_: *mut LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1729_: u8 = 0;
            let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_binderName_1726_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_binderName_1726_);
            v_binderType_1727_ = lean_ctor_get(v_e_1699_, 1);
            lean_inc_ref(v_binderType_1727_);
            v_body_1728_ = lean_ctor_get(v_e_1699_, 2);
            lean_inc_ref(v_body_1728_);
            v_binderInfo_1729_ = lean_ctor_get_uint8(
                v_e_1699_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
            );
            lean_dec_ref_known(v_e_1699_, 3);
            v___x_1730_ = lean_box((v_binderInfo_1729_) as usize);
            v___x_1731_ = lean_apply_4(
                v_h__11_1710_,
                v_binderName_1726_,
                v_binderType_1727_,
                v_body_1728_,
                v___x_1730_,
            );
            return v___x_1731_;
        }
        7 => {
            let mut v_binderName_1732_: *mut LeanObject = core::ptr::null_mut();
            let mut v_binderType_1733_: *mut LeanObject = core::ptr::null_mut();
            let mut v_body_1734_: *mut LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1735_: u8 = 0;
            let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_binderName_1732_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_binderName_1732_);
            v_binderType_1733_ = lean_ctor_get(v_e_1699_, 1);
            lean_inc_ref(v_binderType_1733_);
            v_body_1734_ = lean_ctor_get(v_e_1699_, 2);
            lean_inc_ref(v_body_1734_);
            v_binderInfo_1735_ = lean_ctor_get_uint8(
                v_e_1699_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
            );
            lean_dec_ref_known(v_e_1699_, 3);
            v___x_1736_ = lean_box((v_binderInfo_1735_) as usize);
            v___x_1737_ = lean_apply_4(
                v_h__10_1709_,
                v_binderName_1732_,
                v_binderType_1733_,
                v_body_1734_,
                v___x_1736_,
            );
            return v___x_1737_;
        }
        8 => {
            let mut v_declName_1738_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_1739_: *mut LeanObject = core::ptr::null_mut();
            let mut v_value_1740_: *mut LeanObject = core::ptr::null_mut();
            let mut v_body_1741_: *mut LeanObject = core::ptr::null_mut();
            let mut v_nondep_1742_: u8 = 0;
            let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_declName_1738_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_declName_1738_);
            v_type_1739_ = lean_ctor_get(v_e_1699_, 1);
            lean_inc_ref(v_type_1739_);
            v_value_1740_ = lean_ctor_get(v_e_1699_, 2);
            lean_inc_ref(v_value_1740_);
            v_body_1741_ = lean_ctor_get(v_e_1699_, 3);
            lean_inc_ref(v_body_1741_);
            v_nondep_1742_ = lean_ctor_get_uint8(
                v_e_1699_,
                (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
            );
            lean_dec_ref_known(v_e_1699_, 4);
            v___x_1743_ = lean_box((v_nondep_1742_) as usize);
            v___x_1744_ = lean_apply_5(
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
            let mut v_a_1745_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            v_a_1745_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc_ref(v_a_1745_);
            lean_dec_ref_known(v_e_1699_, 1);
            v___x_1746_ = lean_apply_1(v_h__1_1700_, v_a_1745_);
            return v___x_1746_;
        }
        10 => {
            let mut v_data_1747_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expr_1748_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__9_1708_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_data_1747_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_data_1747_);
            v_expr_1748_ = lean_ctor_get(v_e_1699_, 1);
            lean_inc_ref(v_expr_1748_);
            lean_dec_ref_known(v_e_1699_, 2);
            v___x_1749_ = lean_apply_2(v_h__8_1707_, v_data_1747_, v_expr_1748_);
            return v___x_1749_;
        }
        _ => {
            let mut v_typeName_1750_: *mut LeanObject = core::ptr::null_mut();
            let mut v_idx_1751_: *mut LeanObject = core::ptr::null_mut();
            let mut v_struct_1752_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__12_1711_);
            lean_dec(v_h__11_1710_);
            lean_dec(v_h__10_1709_);
            lean_dec(v_h__8_1707_);
            lean_dec(v_h__7_1706_);
            lean_dec(v_h__6_1705_);
            lean_dec(v_h__5_1704_);
            lean_dec(v_h__4_1703_);
            lean_dec(v_h__3_1702_);
            lean_dec(v_h__2_1701_);
            lean_dec(v_h__1_1700_);
            v_typeName_1750_ = lean_ctor_get(v_e_1699_, 0);
            lean_inc(v_typeName_1750_);
            v_idx_1751_ = lean_ctor_get(v_e_1699_, 1);
            lean_inc(v_idx_1751_);
            v_struct_1752_ = lean_ctor_get(v_e_1699_, 2);
            lean_inc_ref(v_struct_1752_);
            lean_dec_ref_known(v_e_1699_, 3);
            v___x_1753_ = lean_apply_3(v_h__9_1708_, v_typeName_1750_, v_idx_1751_, v_struct_1752_);
            return v___x_1753_;
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Sym_replaceS_x27___closed__0() -> *mut LeanObject {
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    v___x_1754_ = lean_box(0);
    v___x_1755_ = lean_unsigned_to_nat(16);
    v___x_1756_ = lean_mk_array(v___x_1755_, v___x_1754_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_replaceS_x27___closed__1() -> *mut LeanObject {
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    v___x_1757_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS_x27___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS_x27___closed__0_once),
        _init_l_Lean_Meta_Sym_replaceS_x27___closed__0,
    );
    v___x_1758_ = lean_unsigned_to_nat(0);
    v___x_1759_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1759_, 0, v___x_1758_);
    lean_ctor_set(v___x_1759_, 1, v___x_1757_);
    return v___x_1759_;
}
pub unsafe fn l_Lean_Meta_Sym_replaceS_x27(
    mut v_e_1760_: *mut LeanObject,
    mut v_f_1761_: *mut LeanObject,
    mut v_a_1762_: u8,
    mut v_a_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1771_: u8 = 0;
    let mut v_val_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_unused_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1781_: u8 = 0;
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut v_unused_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut v_unused_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v_unused_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1808_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_unused_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v_unused_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v_unused_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_unused_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1764_ = lean_unsigned_to_nat(0);
                v___x_1765_ = lean_box((v_a_1762_) as usize);
                lean_inc_ref(v_f_1761_);
                lean_inc_ref(v_e_1760_);
                v___x_1766_ =
                    lean_apply_4(v_f_1761_, v_e_1760_, v___x_1764_, v___x_1765_, v_a_1763_);
                v_fst_1767_ = lean_ctor_get(v___x_1766_, 0);
                lean_inc(v_fst_1767_);
                if lean_obj_tag(v_fst_1767_) == 1 {
                    lean_dec_ref(v_f_1761_);
                    lean_dec_ref(v_e_1760_);
                    v_snd_1768_ = lean_ctor_get(v___x_1766_, 1);
                    v_isSharedCheck_1776_ = (!lean_is_exclusive(v___x_1766_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v_unused_1777_ = lean_ctor_get(v___x_1766_, 0);
                        lean_dec(v_unused_1777_);
                        v___x_1770_ = v___x_1766_;
                        v_isShared_1771_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1768_);
                        lean_dec(v___x_1766_);
                        v___x_1770_ = lean_box(0);
                        v_isShared_1771_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1767_);
                    match lean_obj_tag(v_e_1760_) {
                        9 => {
                            lean_dec_ref(v_f_1761_);
                            v_snd_1778_ = lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1785_ = (!lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1785_ == 0 {
                                v_unused_1786_ = lean_ctor_get(v___x_1766_, 0);
                                lean_dec(v_unused_1786_);
                                v___x_1780_ = v___x_1766_;
                                v_isShared_1781_ = v_isSharedCheck_1785_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_snd_1778_);
                                lean_dec(v___x_1766_);
                                v___x_1780_ = lean_box(0);
                                v_isShared_1781_ = v_isSharedCheck_1785_;
                                state = 3;
                                continue;
                            }
                        }
                        2 => {
                            lean_dec_ref(v_f_1761_);
                            v_snd_1787_ = lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1794_ = (!lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1794_ == 0 {
                                v_unused_1795_ = lean_ctor_get(v___x_1766_, 0);
                                lean_dec(v_unused_1795_);
                                v___x_1789_ = v___x_1766_;
                                v_isShared_1790_ = v_isSharedCheck_1794_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_snd_1787_);
                                lean_dec(v___x_1766_);
                                v___x_1789_ = lean_box(0);
                                v_isShared_1790_ = v_isSharedCheck_1794_;
                                state = 5;
                                continue;
                            }
                        }
                        0 => {
                            lean_dec_ref(v_f_1761_);
                            v_snd_1796_ = lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1803_ = (!lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1803_ == 0 {
                                v_unused_1804_ = lean_ctor_get(v___x_1766_, 0);
                                lean_dec(v_unused_1804_);
                                v___x_1798_ = v___x_1766_;
                                v_isShared_1799_ = v_isSharedCheck_1803_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_snd_1796_);
                                lean_dec(v___x_1766_);
                                v___x_1798_ = lean_box(0);
                                v_isShared_1799_ = v_isSharedCheck_1803_;
                                state = 7;
                                continue;
                            }
                        }
                        1 => {
                            lean_dec_ref(v_f_1761_);
                            v_snd_1805_ = lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1812_ = (!lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1812_ == 0 {
                                v_unused_1813_ = lean_ctor_get(v___x_1766_, 0);
                                lean_dec(v_unused_1813_);
                                v___x_1807_ = v___x_1766_;
                                v_isShared_1808_ = v_isSharedCheck_1812_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_snd_1805_);
                                lean_dec(v___x_1766_);
                                v___x_1807_ = lean_box(0);
                                v_isShared_1808_ = v_isSharedCheck_1812_;
                                state = 9;
                                continue;
                            }
                        }
                        4 => {
                            lean_dec_ref(v_f_1761_);
                            v_snd_1814_ = lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1821_ = (!lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1821_ == 0 {
                                v_unused_1822_ = lean_ctor_get(v___x_1766_, 0);
                                lean_dec(v_unused_1822_);
                                v___x_1816_ = v___x_1766_;
                                v_isShared_1817_ = v_isSharedCheck_1821_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_snd_1814_);
                                lean_dec(v___x_1766_);
                                v___x_1816_ = lean_box(0);
                                v_isShared_1817_ = v_isSharedCheck_1821_;
                                state = 11;
                                continue;
                            }
                        }
                        3 => {
                            lean_dec_ref(v_f_1761_);
                            v_snd_1823_ = lean_ctor_get(v___x_1766_, 1);
                            v_isSharedCheck_1830_ = (!lean_is_exclusive(v___x_1766_)) as u8;
                            if v_isSharedCheck_1830_ == 0 {
                                v_unused_1831_ = lean_ctor_get(v___x_1766_, 0);
                                lean_dec(v_unused_1831_);
                                v___x_1825_ = v___x_1766_;
                                v_isShared_1826_ = v_isSharedCheck_1830_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_snd_1823_);
                                lean_dec(v___x_1766_);
                                v___x_1825_ = lean_box(0);
                                v_isShared_1826_ = v_isSharedCheck_1830_;
                                state = 13;
                                continue;
                            }
                        }
                        _ => {
                            v_snd_1832_ = lean_ctor_get(v___x_1766_, 1);
                            lean_inc(v_snd_1832_);
                            lean_dec_ref(v___x_1766_);
                            v___x_1833_ = lean_obj_once(
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
                            v_fst_1835_ = lean_ctor_get(v___x_1834_, 0);
                            lean_inc(v_fst_1835_);
                            v_snd_1836_ = lean_ctor_get(v___x_1834_, 1);
                            lean_inc(v_snd_1836_);
                            lean_dec_ref(v___x_1834_);
                            v_fst_1837_ = lean_ctor_get(v_fst_1835_, 0);
                            v_isSharedCheck_1844_ = (!lean_is_exclusive(v_fst_1835_)) as u8;
                            if v_isSharedCheck_1844_ == 0 {
                                v_unused_1845_ = lean_ctor_get(v_fst_1835_, 1);
                                lean_dec(v_unused_1845_);
                                v___x_1839_ = v_fst_1835_;
                                v_isShared_1840_ = v_isSharedCheck_1844_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_fst_1837_);
                                lean_dec(v_fst_1835_);
                                v___x_1839_ = lean_box(0);
                                v_isShared_1840_ = v_isSharedCheck_1844_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_val_1772_ = lean_ctor_get(v_fst_1767_, 0);
                lean_inc(v_val_1772_);
                lean_dec_ref_known(v_fst_1767_, 1);
                if v_isShared_1771_ == 0 {
                    lean_ctor_set(v___x_1770_, 0, v_val_1772_);
                    v___x_1774_ = v___x_1770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_val_1772_);
                    lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_snd_1768_);
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
                    lean_ctor_set(v___x_1780_, 0, v_e_1760_);
                    v___x_1783_ = v___x_1780_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_e_1760_);
                    lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_snd_1778_);
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
                    lean_ctor_set(v___x_1789_, 0, v_e_1760_);
                    v___x_1792_ = v___x_1789_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_e_1760_);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_snd_1787_);
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
                    lean_ctor_set(v___x_1798_, 0, v_e_1760_);
                    v___x_1801_ = v___x_1798_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_e_1760_);
                    lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_snd_1796_);
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
                    lean_ctor_set(v___x_1807_, 0, v_e_1760_);
                    v___x_1810_ = v___x_1807_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_e_1760_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_snd_1805_);
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
                    lean_ctor_set(v___x_1816_, 0, v_e_1760_);
                    v___x_1819_ = v___x_1816_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_e_1760_);
                    lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_snd_1814_);
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
                    lean_ctor_set(v___x_1825_, 0, v_e_1760_);
                    v___x_1828_ = v___x_1825_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_e_1760_);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_snd_1823_);
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
                    lean_ctor_set(v___x_1839_, 1, v_snd_1836_);
                    v___x_1842_ = v___x_1839_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_fst_1837_);
                    lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_snd_1836_);
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
    mut v_e_1846_: *mut LeanObject,
    mut v_f_1847_: *mut LeanObject,
    mut v_a_1848_: *mut LeanObject,
    mut v_a_1849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1850_: u8 = 0;
    let mut v_res_1851_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1850_ = (lean_unbox(v_a_1848_) as u8);
    v_res_1851_ = l_Lean_Meta_Sym_replaceS_x27(v_e_1846_, v_f_1847_, v_a_boxed_1850_, v_a_1849_);
    return v_res_1851_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2() -> *mut LeanObject {
    let mut v___f_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    v___f_1854_ = l_Lean_Meta_Sym_replaceS___redArg___closed__1;
    v___f_1855_ = l_Lean_Meta_Sym_replaceS___redArg___closed__0;
    v___x_1856_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_1855_, v___f_1854_);
    return v___x_1856_;
}
pub unsafe fn l_Lean_Meta_Sym_replaceS___redArg(
    mut v_e_1857_: *mut LeanObject,
    mut v_f_1858_: *mut LeanObject,
    mut v_a_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1872_: u8 = 0;
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1894_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1897_: u8 = 0;
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_unused_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1905_: u8 = 0;
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1861_ = lean_st_ref_take(v_a_1859_);
                v_share_1862_ = lean_ctor_get(v___x_1861_, 0);
                v_maxFVar_1863_ = lean_ctor_get(v___x_1861_, 1);
                v_proofInstInfo_1864_ = lean_ctor_get(v___x_1861_, 2);
                v_inferType_1865_ = lean_ctor_get(v___x_1861_, 3);
                v_getLevel_1866_ = lean_ctor_get(v___x_1861_, 4);
                v_congrInfo_1867_ = lean_ctor_get(v___x_1861_, 5);
                v_defEqI_1868_ = lean_ctor_get(v___x_1861_, 6);
                v_extensions_1869_ = lean_ctor_get(v___x_1861_, 7);
                v_issues_1870_ = lean_ctor_get(v___x_1861_, 8);
                v_canon_1871_ = lean_ctor_get(v___x_1861_, 9);
                v_debug_1872_ = lean_ctor_get_uint8(
                    v___x_1861_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1925_ = (!lean_is_exclusive(v___x_1861_)) as u8;
                if v_isSharedCheck_1925_ == 0 {
                    v___x_1874_ = v___x_1861_;
                    v_isShared_1875_ = v_isSharedCheck_1925_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_1871_);
                    lean_inc(v_issues_1870_);
                    lean_inc(v_extensions_1869_);
                    lean_inc(v_defEqI_1868_);
                    lean_inc(v_congrInfo_1867_);
                    lean_inc(v_getLevel_1866_);
                    lean_inc(v_inferType_1865_);
                    lean_inc(v_proofInstInfo_1864_);
                    lean_inc(v_maxFVar_1863_);
                    lean_inc(v_share_1862_);
                    lean_dec(v___x_1861_);
                    v___x_1874_ = lean_box(0);
                    v_isShared_1875_ = v_isSharedCheck_1925_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1876_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS___redArg___closed__2_once),
                    _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2,
                );
                if v_isShared_1875_ == 0 {
                    lean_ctor_set(v___x_1874_, 0, v___x_1876_);
                    v___x_1878_ = v___x_1874_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1876_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_maxFVar_1863_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_proofInstInfo_1864_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_inferType_1865_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 4, v_getLevel_1866_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 5, v_congrInfo_1867_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 6, v_defEqI_1868_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 7, v_extensions_1869_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 8, v_issues_1870_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 9, v_canon_1871_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1924_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                v_debug_1905_ = lean_ctor_get_uint8(
                    v___x_1880_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_1880_);
                v___x_1906_ = lean_unsigned_to_nat(0);
                v___x_1907_ = lean_box((v_debug_1905_) as usize);
                lean_inc_ref(v_f_1858_);
                lean_inc_ref(v_e_1857_);
                v___x_1908_ = lean_apply_4(
                    v_f_1858_,
                    v_e_1857_,
                    v___x_1906_,
                    v___x_1907_,
                    v_share_1862_,
                );
                v_fst_1909_ = lean_ctor_get(v___x_1908_, 0);
                lean_inc(v_fst_1909_);
                if lean_obj_tag(v_fst_1909_) == 1 {
                    lean_dec_ref(v_f_1858_);
                    lean_dec_ref(v_e_1857_);
                    v_snd_1910_ = lean_ctor_get(v___x_1908_, 1);
                    lean_inc(v_snd_1910_);
                    lean_dec_ref(v___x_1908_);
                    v_val_1911_ = lean_ctor_get(v_fst_1909_, 0);
                    lean_inc(v_val_1911_);
                    lean_dec_ref_known(v_fst_1909_, 1);
                    v_fst_1882_ = v_val_1911_;
                    v_snd_1883_ = v_snd_1910_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_fst_1909_);
                    match lean_obj_tag(v_e_1857_) {
                        9 => {
                            lean_dec_ref(v_f_1858_);
                            v_snd_1912_ = lean_ctor_get(v___x_1908_, 1);
                            lean_inc(v_snd_1912_);
                            lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1912_;
                            state = 3;
                            continue;
                        }
                        2 => {
                            lean_dec_ref(v_f_1858_);
                            v_snd_1913_ = lean_ctor_get(v___x_1908_, 1);
                            lean_inc(v_snd_1913_);
                            lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1913_;
                            state = 3;
                            continue;
                        }
                        0 => {
                            lean_dec_ref(v_f_1858_);
                            v_snd_1914_ = lean_ctor_get(v___x_1908_, 1);
                            lean_inc(v_snd_1914_);
                            lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1914_;
                            state = 3;
                            continue;
                        }
                        1 => {
                            lean_dec_ref(v_f_1858_);
                            v_snd_1915_ = lean_ctor_get(v___x_1908_, 1);
                            lean_inc(v_snd_1915_);
                            lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1915_;
                            state = 3;
                            continue;
                        }
                        4 => {
                            lean_dec_ref(v_f_1858_);
                            v_snd_1916_ = lean_ctor_get(v___x_1908_, 1);
                            lean_inc(v_snd_1916_);
                            lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1916_;
                            state = 3;
                            continue;
                        }
                        3 => {
                            lean_dec_ref(v_f_1858_);
                            v_snd_1917_ = lean_ctor_get(v___x_1908_, 1);
                            lean_inc(v_snd_1917_);
                            lean_dec_ref(v___x_1908_);
                            v_fst_1882_ = v_e_1857_;
                            v_snd_1883_ = v_snd_1917_;
                            state = 3;
                            continue;
                        }
                        _ => {
                            v_snd_1918_ = lean_ctor_get(v___x_1908_, 1);
                            lean_inc(v_snd_1918_);
                            lean_dec_ref(v___x_1908_);
                            v___x_1919_ = lean_obj_once(
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
                            v_fst_1921_ = lean_ctor_get(v___x_1920_, 0);
                            lean_inc(v_fst_1921_);
                            v_snd_1922_ = lean_ctor_get(v___x_1920_, 1);
                            lean_inc(v_snd_1922_);
                            lean_dec_ref(v___x_1920_);
                            v_fst_1923_ = lean_ctor_get(v_fst_1921_, 0);
                            lean_inc(v_fst_1923_);
                            lean_dec(v_fst_1921_);
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
                v_maxFVar_1885_ = lean_ctor_get(v___x_1884_, 1);
                v_proofInstInfo_1886_ = lean_ctor_get(v___x_1884_, 2);
                v_inferType_1887_ = lean_ctor_get(v___x_1884_, 3);
                v_getLevel_1888_ = lean_ctor_get(v___x_1884_, 4);
                v_congrInfo_1889_ = lean_ctor_get(v___x_1884_, 5);
                v_defEqI_1890_ = lean_ctor_get(v___x_1884_, 6);
                v_extensions_1891_ = lean_ctor_get(v___x_1884_, 7);
                v_issues_1892_ = lean_ctor_get(v___x_1884_, 8);
                v_canon_1893_ = lean_ctor_get(v___x_1884_, 9);
                v_debug_1894_ = lean_ctor_get_uint8(
                    v___x_1884_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1903_ = (!lean_is_exclusive(v___x_1884_)) as u8;
                if v_isSharedCheck_1903_ == 0 {
                    v_unused_1904_ = lean_ctor_get(v___x_1884_, 0);
                    lean_dec(v_unused_1904_);
                    v___x_1896_ = v___x_1884_;
                    v_isShared_1897_ = v_isSharedCheck_1903_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_canon_1893_);
                    lean_inc(v_issues_1892_);
                    lean_inc(v_extensions_1891_);
                    lean_inc(v_defEqI_1890_);
                    lean_inc(v_congrInfo_1889_);
                    lean_inc(v_getLevel_1888_);
                    lean_inc(v_inferType_1887_);
                    lean_inc(v_proofInstInfo_1886_);
                    lean_inc(v_maxFVar_1885_);
                    lean_dec(v___x_1884_);
                    v___x_1896_ = lean_box(0);
                    v_isShared_1897_ = v_isSharedCheck_1903_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1897_ == 0 {
                    lean_ctor_set(v___x_1896_, 0, v_snd_1883_);
                    v___x_1899_ = v___x_1896_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_snd_1883_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_maxFVar_1885_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_proofInstInfo_1886_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_inferType_1887_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_getLevel_1888_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 5, v_congrInfo_1889_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 6, v_defEqI_1890_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 7, v_extensions_1891_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 8, v_issues_1892_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 9, v_canon_1893_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1902_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_1894_,
                    );
                    v___x_1899_ = v_reuseFailAlloc_1902_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1900_ = lean_st_ref_set(v_a_1859_, v___x_1899_);
                v___x_1901_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1901_, 0, v_fst_1882_);
                return v___x_1901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_replaceS___redArg___boxed(
    mut v_e_1926_: *mut LeanObject,
    mut v_f_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
    mut v_a_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1930_: *mut LeanObject = core::ptr::null_mut();
    v_res_1930_ = l_Lean_Meta_Sym_replaceS___redArg(v_e_1926_, v_f_1927_, v_a_1928_);
    lean_dec(v_a_1928_);
    return v_res_1930_;
}
pub unsafe fn l_Lean_Meta_Sym_replaceS(
    mut v_e_1931_: *mut LeanObject,
    mut v_f_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
    mut v_a_1934_: *mut LeanObject,
    mut v_a_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
    mut v_a_1937_: *mut LeanObject,
    mut v_a_1938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1951_: u8 = 0;
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1954_: u8 = 0;
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1973_: u8 = 0;
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut v_unused_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1984_: u8 = 0;
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1940_ = lean_st_ref_take(v_a_1934_);
                v_share_1941_ = lean_ctor_get(v___x_1940_, 0);
                v_maxFVar_1942_ = lean_ctor_get(v___x_1940_, 1);
                v_proofInstInfo_1943_ = lean_ctor_get(v___x_1940_, 2);
                v_inferType_1944_ = lean_ctor_get(v___x_1940_, 3);
                v_getLevel_1945_ = lean_ctor_get(v___x_1940_, 4);
                v_congrInfo_1946_ = lean_ctor_get(v___x_1940_, 5);
                v_defEqI_1947_ = lean_ctor_get(v___x_1940_, 6);
                v_extensions_1948_ = lean_ctor_get(v___x_1940_, 7);
                v_issues_1949_ = lean_ctor_get(v___x_1940_, 8);
                v_canon_1950_ = lean_ctor_get(v___x_1940_, 9);
                v_debug_1951_ = lean_ctor_get_uint8(
                    v___x_1940_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2004_ = (!lean_is_exclusive(v___x_1940_)) as u8;
                if v_isSharedCheck_2004_ == 0 {
                    v___x_1953_ = v___x_1940_;
                    v_isShared_1954_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_1950_);
                    lean_inc(v_issues_1949_);
                    lean_inc(v_extensions_1948_);
                    lean_inc(v_defEqI_1947_);
                    lean_inc(v_congrInfo_1946_);
                    lean_inc(v_getLevel_1945_);
                    lean_inc(v_inferType_1944_);
                    lean_inc(v_proofInstInfo_1943_);
                    lean_inc(v_maxFVar_1942_);
                    lean_inc(v_share_1941_);
                    lean_dec(v___x_1940_);
                    v___x_1953_ = lean_box(0);
                    v_isShared_1954_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1955_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_replaceS___redArg___closed__2_once),
                    _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2,
                );
                if v_isShared_1954_ == 0 {
                    lean_ctor_set(v___x_1953_, 0, v___x_1955_);
                    v___x_1957_ = v___x_1953_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1955_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_maxFVar_1942_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_proofInstInfo_1943_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_inferType_1944_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_getLevel_1945_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 5, v_congrInfo_1946_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 6, v_defEqI_1947_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 7, v_extensions_1948_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 8, v_issues_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 9, v_canon_1950_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2003_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                v_debug_1984_ = lean_ctor_get_uint8(
                    v___x_1959_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_1959_);
                v___x_1985_ = lean_unsigned_to_nat(0);
                v___x_1986_ = lean_box((v_debug_1984_) as usize);
                lean_inc_ref(v_f_1932_);
                lean_inc_ref(v_e_1931_);
                v___x_1987_ = lean_apply_4(
                    v_f_1932_,
                    v_e_1931_,
                    v___x_1985_,
                    v___x_1986_,
                    v_share_1941_,
                );
                v_fst_1988_ = lean_ctor_get(v___x_1987_, 0);
                lean_inc(v_fst_1988_);
                if lean_obj_tag(v_fst_1988_) == 1 {
                    lean_dec_ref(v_f_1932_);
                    lean_dec_ref(v_e_1931_);
                    v_snd_1989_ = lean_ctor_get(v___x_1987_, 1);
                    lean_inc(v_snd_1989_);
                    lean_dec_ref(v___x_1987_);
                    v_val_1990_ = lean_ctor_get(v_fst_1988_, 0);
                    lean_inc(v_val_1990_);
                    lean_dec_ref_known(v_fst_1988_, 1);
                    v_fst_1961_ = v_val_1990_;
                    v_snd_1962_ = v_snd_1989_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_fst_1988_);
                    match lean_obj_tag(v_e_1931_) {
                        9 => {
                            lean_dec_ref(v_f_1932_);
                            v_snd_1991_ = lean_ctor_get(v___x_1987_, 1);
                            lean_inc(v_snd_1991_);
                            lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1991_;
                            state = 3;
                            continue;
                        }
                        2 => {
                            lean_dec_ref(v_f_1932_);
                            v_snd_1992_ = lean_ctor_get(v___x_1987_, 1);
                            lean_inc(v_snd_1992_);
                            lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1992_;
                            state = 3;
                            continue;
                        }
                        0 => {
                            lean_dec_ref(v_f_1932_);
                            v_snd_1993_ = lean_ctor_get(v___x_1987_, 1);
                            lean_inc(v_snd_1993_);
                            lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1993_;
                            state = 3;
                            continue;
                        }
                        1 => {
                            lean_dec_ref(v_f_1932_);
                            v_snd_1994_ = lean_ctor_get(v___x_1987_, 1);
                            lean_inc(v_snd_1994_);
                            lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1994_;
                            state = 3;
                            continue;
                        }
                        4 => {
                            lean_dec_ref(v_f_1932_);
                            v_snd_1995_ = lean_ctor_get(v___x_1987_, 1);
                            lean_inc(v_snd_1995_);
                            lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1995_;
                            state = 3;
                            continue;
                        }
                        3 => {
                            lean_dec_ref(v_f_1932_);
                            v_snd_1996_ = lean_ctor_get(v___x_1987_, 1);
                            lean_inc(v_snd_1996_);
                            lean_dec_ref(v___x_1987_);
                            v_fst_1961_ = v_e_1931_;
                            v_snd_1962_ = v_snd_1996_;
                            state = 3;
                            continue;
                        }
                        _ => {
                            v_snd_1997_ = lean_ctor_get(v___x_1987_, 1);
                            lean_inc(v_snd_1997_);
                            lean_dec_ref(v___x_1987_);
                            v___x_1998_ = lean_obj_once(
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
                            v_fst_2000_ = lean_ctor_get(v___x_1999_, 0);
                            lean_inc(v_fst_2000_);
                            v_snd_2001_ = lean_ctor_get(v___x_1999_, 1);
                            lean_inc(v_snd_2001_);
                            lean_dec_ref(v___x_1999_);
                            v_fst_2002_ = lean_ctor_get(v_fst_2000_, 0);
                            lean_inc(v_fst_2002_);
                            lean_dec(v_fst_2000_);
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
                v_maxFVar_1964_ = lean_ctor_get(v___x_1963_, 1);
                v_proofInstInfo_1965_ = lean_ctor_get(v___x_1963_, 2);
                v_inferType_1966_ = lean_ctor_get(v___x_1963_, 3);
                v_getLevel_1967_ = lean_ctor_get(v___x_1963_, 4);
                v_congrInfo_1968_ = lean_ctor_get(v___x_1963_, 5);
                v_defEqI_1969_ = lean_ctor_get(v___x_1963_, 6);
                v_extensions_1970_ = lean_ctor_get(v___x_1963_, 7);
                v_issues_1971_ = lean_ctor_get(v___x_1963_, 8);
                v_canon_1972_ = lean_ctor_get(v___x_1963_, 9);
                v_debug_1973_ = lean_ctor_get_uint8(
                    v___x_1963_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1982_ = (!lean_is_exclusive(v___x_1963_)) as u8;
                if v_isSharedCheck_1982_ == 0 {
                    v_unused_1983_ = lean_ctor_get(v___x_1963_, 0);
                    lean_dec(v_unused_1983_);
                    v___x_1975_ = v___x_1963_;
                    v_isShared_1976_ = v_isSharedCheck_1982_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_canon_1972_);
                    lean_inc(v_issues_1971_);
                    lean_inc(v_extensions_1970_);
                    lean_inc(v_defEqI_1969_);
                    lean_inc(v_congrInfo_1968_);
                    lean_inc(v_getLevel_1967_);
                    lean_inc(v_inferType_1966_);
                    lean_inc(v_proofInstInfo_1965_);
                    lean_inc(v_maxFVar_1964_);
                    lean_dec(v___x_1963_);
                    v___x_1975_ = lean_box(0);
                    v_isShared_1976_ = v_isSharedCheck_1982_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1976_ == 0 {
                    lean_ctor_set(v___x_1975_, 0, v_snd_1962_);
                    v___x_1978_ = v___x_1975_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_snd_1962_);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_maxFVar_1964_);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_proofInstInfo_1965_);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_inferType_1966_);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_getLevel_1967_);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_congrInfo_1968_);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_defEqI_1969_);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_extensions_1970_);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_issues_1971_);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 9, v_canon_1972_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1981_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_1973_,
                    );
                    v___x_1978_ = v_reuseFailAlloc_1981_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1979_ = lean_st_ref_set(v_a_1934_, v___x_1978_);
                v___x_1980_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1980_, 0, v_fst_1961_);
                return v___x_1980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_replaceS___boxed(
    mut v_e_2005_: *mut LeanObject,
    mut v_f_2006_: *mut LeanObject,
    mut v_a_2007_: *mut LeanObject,
    mut v_a_2008_: *mut LeanObject,
    mut v_a_2009_: *mut LeanObject,
    mut v_a_2010_: *mut LeanObject,
    mut v_a_2011_: *mut LeanObject,
    mut v_a_2012_: *mut LeanObject,
    mut v_a_2013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2014_: *mut LeanObject = core::ptr::null_mut();
    v_res_2014_ = l_Lean_Meta_Sym_replaceS(
        v_e_2005_, v_f_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_,
    );
    lean_dec(v_a_2012_);
    lean_dec_ref(v_a_2011_);
    lean_dec(v_a_2010_);
    lean_dec_ref(v_a_2009_);
    lean_dec(v_a_2008_);
    lean_dec_ref(v_a_2007_);
    return v_res_2014_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_ReplaceS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_ReplaceS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_ReplaceS(builtin);
}
