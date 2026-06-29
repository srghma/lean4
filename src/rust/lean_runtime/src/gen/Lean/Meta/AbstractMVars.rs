// Lean compiler output
// Module: Lean.Meta.AbstractMVars
// Imports: Lean.Meta.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{l_StateT_bind, l_StateT_get};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::l_Lean_Name_num___override;
use crate::r#gen::Init::Util::l_ptrEqList___redArg;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_hasMVar, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_instBEqBinderInfo_beq, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_hasMVar, l_Lean_Level_succ___override, l_Lean_instBEqLevelMVarId_beq,
    l_Lean_instHashableLevelMVarId_hash, l_Lean_mkLevelIMax_x27, l_Lean_mkLevelMax_x27,
    l_Lean_mkLevelParam, l_Lean_simpLevelIMax_x27, l_Lean_simpLevelMax_x27,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_mkLambda, l_Lean_LocalContext_mkLocalDecl,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_AbstractMVarsResult_numMVars,
    l_Lean_Meta_lambdaMetaTelescope, l_Lean_Meta_mkFreshLevelMVar,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_getDecl, l_Lean_MetavarContext_getLevelDepth, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::InstantiateLevelParams::l_Lean_Expr_instantiateLevelParamsArray;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value:
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
    m_fun: l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value:
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
    m_fun: l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value:
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
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value:
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
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value:
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
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value:
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
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value:
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
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value:
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
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value:
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
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value:
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
    m_fun: l_StateT_get as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value:
    crate::leanh::LeanClosureObject<7> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_bind as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 7,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [95, 97, 98, 115, 116, 77, 86, 97, 114, 0]};
static mut l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value) as *mut crate::leanh::LeanObject,6357867680762384532 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [120, 0],
};
static mut l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13655884332201764339 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_abstractMVars___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_abstractMVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_abstractMVars___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_abstractMVars___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_abstractMVars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_abstractMVars___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_abstractMVars___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(
    mut v_____do__lift_1163_: *mut crate::leanh::LeanObject,
    mut v___y_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mctx_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mctx_1165_ = crate::leanh::lean_ctor_get(v_____do__lift_1163_, 2);
    crate::leanh::lean_inc_ref(v_mctx_1165_);
    v___x_1166_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1166_, 0, v_mctx_1165_);
    crate::leanh::lean_ctor_set(v___x_1166_, 1, v___y_1164_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed(
    mut v_____do__lift_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ =
        l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(v_____do__lift_1167_, v___y_1168_);
    crate::leanh::lean_dec_ref(v_____do__lift_1167_);
    return v_res_1169_;
}
pub unsafe fn l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1(
    mut v_f_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ngen_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1181_: u8 = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ngen_1172_ = crate::leanh::lean_ctor_get(v___y_1171_, 0);
                v_lctx_1173_ = crate::leanh::lean_ctor_get(v___y_1171_, 1);
                v_mctx_1174_ = crate::leanh::lean_ctor_get(v___y_1171_, 2);
                v_nextParamIdx_1175_ = crate::leanh::lean_ctor_get(v___y_1171_, 3);
                v_paramNames_1176_ = crate::leanh::lean_ctor_get(v___y_1171_, 4);
                v_fvars_1177_ = crate::leanh::lean_ctor_get(v___y_1171_, 5);
                v_mvars_1178_ = crate::leanh::lean_ctor_get(v___y_1171_, 6);
                v_lmap_1179_ = crate::leanh::lean_ctor_get(v___y_1171_, 7);
                v_emap_1180_ = crate::leanh::lean_ctor_get(v___y_1171_, 8);
                v_abstractLevels_1181_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1171_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_isSharedCheck_1191_ = (!crate::leanh::lean_is_exclusive(v___y_1171_)) as u8;
                if v_isSharedCheck_1191_ == 0 {
                    v___x_1183_ = v___y_1171_;
                    v_isShared_1184_ = v_isSharedCheck_1191_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_emap_1180_);
                    crate::leanh::lean_inc(v_lmap_1179_);
                    crate::leanh::lean_inc(v_mvars_1178_);
                    crate::leanh::lean_inc(v_fvars_1177_);
                    crate::leanh::lean_inc(v_paramNames_1176_);
                    crate::leanh::lean_inc(v_nextParamIdx_1175_);
                    crate::leanh::lean_inc(v_mctx_1174_);
                    crate::leanh::lean_inc(v_lctx_1173_);
                    crate::leanh::lean_inc(v_ngen_1172_);
                    crate::leanh::lean_dec(v___y_1171_);
                    v___x_1183_ = crate::leanh::lean_box(0);
                    v_isShared_1184_ = v_isSharedCheck_1191_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1185_ = crate::leanh::lean_box(0);
                v___x_1186_ = crate::leanh::lean_apply_1(v_f_1170_, v_mctx_1174_);
                if v_isShared_1184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1183_, 2, v___x_1186_);
                    v___x_1188_ = v___x_1183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1190_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_ngen_1172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_lctx_1173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 2, v___x_1186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_nextParamIdx_1175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_paramNames_1176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 5, v_fvars_1177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 6, v_mvars_1178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 7, v_lmap_1179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 8, v_emap_1180_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1190_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1181_,
                    );
                    v___x_1188_ = v_reuseFailAlloc_1190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1189_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1189_, 0, v___x_1185_);
                crate::leanh::lean_ctor_set(v___x_1189_, 1, v___x_1188_);
                return v___x_1189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractMVars_mkFreshId(
    mut v_a_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ngen_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1233_: u8 = 0;
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v_namePrefix_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1241_: u8 = 0;
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_isSharedCheck_1253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ngen_1224_ = crate::leanh::lean_ctor_get(v_a_1223_, 0);
                v_lctx_1225_ = crate::leanh::lean_ctor_get(v_a_1223_, 1);
                v_mctx_1226_ = crate::leanh::lean_ctor_get(v_a_1223_, 2);
                v_nextParamIdx_1227_ = crate::leanh::lean_ctor_get(v_a_1223_, 3);
                v_paramNames_1228_ = crate::leanh::lean_ctor_get(v_a_1223_, 4);
                v_fvars_1229_ = crate::leanh::lean_ctor_get(v_a_1223_, 5);
                v_mvars_1230_ = crate::leanh::lean_ctor_get(v_a_1223_, 6);
                v_lmap_1231_ = crate::leanh::lean_ctor_get(v_a_1223_, 7);
                v_emap_1232_ = crate::leanh::lean_ctor_get(v_a_1223_, 8);
                v_abstractLevels_1233_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1223_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_isSharedCheck_1253_ = (!crate::leanh::lean_is_exclusive(v_a_1223_)) as u8;
                if v_isSharedCheck_1253_ == 0 {
                    v___x_1235_ = v_a_1223_;
                    v_isShared_1236_ = v_isSharedCheck_1253_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_emap_1232_);
                    crate::leanh::lean_inc(v_lmap_1231_);
                    crate::leanh::lean_inc(v_mvars_1230_);
                    crate::leanh::lean_inc(v_fvars_1229_);
                    crate::leanh::lean_inc(v_paramNames_1228_);
                    crate::leanh::lean_inc(v_nextParamIdx_1227_);
                    crate::leanh::lean_inc(v_mctx_1226_);
                    crate::leanh::lean_inc(v_lctx_1225_);
                    crate::leanh::lean_inc(v_ngen_1224_);
                    crate::leanh::lean_dec(v_a_1223_);
                    v___x_1235_ = crate::leanh::lean_box(0);
                    v_isShared_1236_ = v_isSharedCheck_1253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_namePrefix_1237_ = crate::leanh::lean_ctor_get(v_ngen_1224_, 0);
                v_idx_1238_ = crate::leanh::lean_ctor_get(v_ngen_1224_, 1);
                v_isSharedCheck_1252_ = (!crate::leanh::lean_is_exclusive(v_ngen_1224_)) as u8;
                if v_isSharedCheck_1252_ == 0 {
                    v___x_1240_ = v_ngen_1224_;
                    v_isShared_1241_ = v_isSharedCheck_1252_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1238_);
                    crate::leanh::lean_inc(v_namePrefix_1237_);
                    crate::leanh::lean_dec(v_ngen_1224_);
                    v___x_1240_ = crate::leanh::lean_box(0);
                    v_isShared_1241_ = v_isSharedCheck_1252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_1238_);
                crate::leanh::lean_inc(v_namePrefix_1237_);
                v___x_1242_ = l_Lean_Name_num___override(v_namePrefix_1237_, v_idx_1238_);
                v___x_1243_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1244_ = lean_nat_add(v_idx_1238_, v___x_1243_);
                crate::leanh::lean_dec(v_idx_1238_);
                if v_isShared_1241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1240_, 1, v___x_1244_);
                    v___x_1246_ = v___x_1240_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_namePrefix_1237_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1244_);
                    v___x_1246_ = v_reuseFailAlloc_1251_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1235_, 0, v___x_1246_);
                    v___x_1248_ = v___x_1235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1246_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_lctx_1225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_mctx_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_nextParamIdx_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_paramNames_1228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 5, v_fvars_1229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 6, v_mvars_1230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 7, v_lmap_1231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 8, v_emap_1232_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1250_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1233_,
                    );
                    v___x_1248_ = v_reuseFailAlloc_1250_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1249_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1249_, 0, v___x_1242_);
                crate::leanh::lean_ctor_set(v___x_1249_, 1, v___x_1248_);
                return v___x_1249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractMVars_mkFreshFVarId(
    mut v_a_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1255_ = l_Lean_Meta_AbstractMVars_mkFreshId(v_a_1254_);
                v_fst_1256_ = crate::leanh::lean_ctor_get(v___x_1255_, 0);
                v_snd_1257_ = crate::leanh::lean_ctor_get(v___x_1255_, 1);
                v_isSharedCheck_1264_ = (!crate::leanh::lean_is_exclusive(v___x_1255_)) as u8;
                if v_isSharedCheck_1264_ == 0 {
                    v___x_1259_ = v___x_1255_;
                    v_isShared_1260_ = v_isSharedCheck_1264_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1257_);
                    crate::leanh::lean_inc(v_fst_1256_);
                    crate::leanh::lean_dec(v___x_1255_);
                    v___x_1259_ = crate::leanh::lean_box(0);
                    v_isShared_1260_ = v_isSharedCheck_1264_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1260_ == 0 {
                    v___x_1262_ = v___x_1259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1263_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_fst_1256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_snd_1257_);
                    v___x_1262_ = v_reuseFailAlloc_1263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_1265_: *mut crate::leanh::LeanObject,
    mut v_x_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: u64 = 0;
    let mut v___x_1275_: u64 = 0;
    let mut v___x_1276_: u64 = 0;
    let mut v_fold_1277_: u64 = 0;
    let mut v___x_1278_: u64 = 0;
    let mut v___x_1279_: u64 = 0;
    let mut v___x_1280_: u64 = 0;
    let mut v___x_1281_: usize = 0;
    let mut v___x_1282_: usize = 0;
    let mut v___x_1283_: usize = 0;
    let mut v___x_1284_: usize = 0;
    let mut v___x_1285_: usize = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1266_) == 0 {
                    return v_x_1265_;
                } else {
                    v_key_1267_ = crate::leanh::lean_ctor_get(v_x_1266_, 0);
                    v_value_1268_ = crate::leanh::lean_ctor_get(v_x_1266_, 1);
                    v_tail_1269_ = crate::leanh::lean_ctor_get(v_x_1266_, 2);
                    v_isSharedCheck_1292_ = (!crate::leanh::lean_is_exclusive(v_x_1266_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1271_ = v_x_1266_;
                        v_isShared_1272_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1269_);
                        crate::leanh::lean_inc(v_value_1268_);
                        crate::leanh::lean_inc(v_key_1267_);
                        crate::leanh::lean_dec(v_x_1266_);
                        v___x_1271_ = crate::leanh::lean_box(0);
                        v_isShared_1272_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1273_ = lean_array_get_size(v_x_1265_);
                v___x_1274_ = l_Lean_instHashableLevelMVarId_hash(v_key_1267_);
                v___x_1275_ = 32u64;
                v___x_1276_ = lean_uint64_shift_right(v___x_1274_, v___x_1275_);
                v_fold_1277_ = lean_uint64_xor(v___x_1274_, v___x_1276_);
                v___x_1278_ = 16u64;
                v___x_1279_ = lean_uint64_shift_right(v_fold_1277_, v___x_1278_);
                v___x_1280_ = lean_uint64_xor(v_fold_1277_, v___x_1279_);
                v___x_1281_ = lean_uint64_to_usize(v___x_1280_);
                v___x_1282_ = lean_usize_of_nat(v___x_1273_);
                v___x_1283_ = 1usize;
                v___x_1284_ = lean_usize_sub(v___x_1282_, v___x_1283_);
                v___x_1285_ = lean_usize_land(v___x_1281_, v___x_1284_);
                v___x_1286_ = lean_array_uget_borrowed(v_x_1265_, v___x_1285_);
                crate::leanh::lean_inc(v___x_1286_);
                if v_isShared_1272_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1271_, 2, v___x_1286_);
                    v___x_1288_ = v___x_1271_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_key_1267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_value_1268_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 2, v___x_1286_);
                    v___x_1288_ = v_reuseFailAlloc_1291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1289_ = lean_array_uset(v_x_1265_, v___x_1285_, v___x_1288_);
                v_x_1265_ = v___x_1289_;
                v_x_1266_ = v_tail_1269_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(
    mut v_i_1293_: *mut crate::leanh::LeanObject,
    mut v_source_1294_: *mut crate::leanh::LeanObject,
    mut v_target_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v_es_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1296_ = lean_array_get_size(v_source_1294_);
                v___x_1297_ = lean_nat_dec_lt(v_i_1293_, v___x_1296_);
                if v___x_1297_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1294_);
                    crate::leanh::lean_dec(v_i_1293_);
                    return v_target_1295_;
                } else {
                    v_es_1298_ = lean_array_fget(v_source_1294_, v_i_1293_);
                    v___x_1299_ = crate::leanh::lean_box(0);
                    v_source_1300_ = lean_array_fset(v_source_1294_, v_i_1293_, v___x_1299_);
                    v_target_1301_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1295_, v_es_1298_);
                    v___x_1302_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1303_ = lean_nat_add(v_i_1293_, v___x_1302_);
                    crate::leanh::lean_dec(v_i_1293_);
                    v_i_1293_ = v___x_1303_;
                    v_source_1294_ = v_source_1300_;
                    v_target_1295_ = v_target_1301_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(
    mut v_data_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1306_ = lean_array_get_size(v_data_1305_);
    v___x_1307_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1308_ = lean_nat_mul(v___x_1306_, v___x_1307_);
    v___x_1309_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1310_ = crate::leanh::lean_box(0);
    v___x_1311_ = lean_mk_array(v_nbuckets_1308_, v___x_1310_);
    v___x_1312_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v___x_1309_, v_data_1305_, v___x_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(
    mut v_a_1313_: *mut crate::leanh::LeanObject,
    mut v_b_1314_: *mut crate::leanh::LeanObject,
    mut v_x_1315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1315_) == 0 {
                    crate::leanh::lean_dec(v_b_1314_);
                    crate::leanh::lean_dec(v_a_1313_);
                    return v_x_1315_;
                } else {
                    v_key_1316_ = crate::leanh::lean_ctor_get(v_x_1315_, 0);
                    v_value_1317_ = crate::leanh::lean_ctor_get(v_x_1315_, 1);
                    v_tail_1318_ = crate::leanh::lean_ctor_get(v_x_1315_, 2);
                    v_isSharedCheck_1330_ = (!crate::leanh::lean_is_exclusive(v_x_1315_)) as u8;
                    if v_isSharedCheck_1330_ == 0 {
                        v___x_1320_ = v_x_1315_;
                        v_isShared_1321_ = v_isSharedCheck_1330_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1318_);
                        crate::leanh::lean_inc(v_value_1317_);
                        crate::leanh::lean_inc(v_key_1316_);
                        crate::leanh::lean_dec(v_x_1315_);
                        v___x_1320_ = crate::leanh::lean_box(0);
                        v_isShared_1321_ = v_isSharedCheck_1330_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1322_ = l_Lean_instBEqLevelMVarId_beq(v_key_1316_, v_a_1313_);
                if v___x_1322_ == 0 {
                    v___x_1323_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_1313_, v_b_1314_, v_tail_1318_);
                    if v_isShared_1321_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1320_, 2, v___x_1323_);
                        v___x_1325_ = v___x_1320_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1326_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_key_1316_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_value_1317_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 2, v___x_1323_);
                        v___x_1325_ = v_reuseFailAlloc_1326_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1317_);
                    crate::leanh::lean_dec(v_key_1316_);
                    if v_isShared_1321_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1320_, 1, v_b_1314_);
                        crate::leanh::lean_ctor_set(v___x_1320_, 0, v_a_1313_);
                        v___x_1328_ = v___x_1320_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1329_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_b_1314_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_tail_1318_);
                        v___x_1328_ = v_reuseFailAlloc_1329_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1325_;
            }
            3 => {
                return v___x_1328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(
    mut v_a_1331_: *mut crate::leanh::LeanObject,
    mut v_x_1332_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1333_: u8 = 0;
    let mut v_key_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1332_) == 0 {
                    v___x_1333_ = 0;
                    return v___x_1333_;
                } else {
                    v_key_1334_ = crate::leanh::lean_ctor_get(v_x_1332_, 0);
                    v_tail_1335_ = crate::leanh::lean_ctor_get(v_x_1332_, 2);
                    v___x_1336_ = l_Lean_instBEqLevelMVarId_beq(v_key_1334_, v_a_1331_);
                    if v___x_1336_ == 0 {
                        v_x_1332_ = v_tail_1335_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1336_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg___boxed(
    mut v_a_1338_: *mut crate::leanh::LeanObject,
    mut v_x_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1340_: u8 = 0;
    let mut v_r_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_1338_, v_x_1339_);
    crate::leanh::lean_dec(v_x_1339_);
    crate::leanh::lean_dec(v_a_1338_);
    v_r_1341_ = crate::leanh::lean_box((v_res_1340_) as usize);
    return v_r_1341_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(
    mut v_m_1342_: *mut crate::leanh::LeanObject,
    mut v_a_1343_: *mut crate::leanh::LeanObject,
    mut v_b_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u64 = 0;
    let mut v___x_1352_: u64 = 0;
    let mut v___x_1353_: u64 = 0;
    let mut v_fold_1354_: u64 = 0;
    let mut v___x_1355_: u64 = 0;
    let mut v___x_1356_: u64 = 0;
    let mut v___x_1357_: u64 = 0;
    let mut v___x_1358_: usize = 0;
    let mut v___x_1359_: usize = 0;
    let mut v___x_1360_: usize = 0;
    let mut v___x_1361_: usize = 0;
    let mut v___x_1362_: usize = 0;
    let mut v_bkt_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v_val_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1345_ = crate::leanh::lean_ctor_get(v_m_1342_, 0);
                v_buckets_1346_ = crate::leanh::lean_ctor_get(v_m_1342_, 1);
                v_isSharedCheck_1389_ = (!crate::leanh::lean_is_exclusive(v_m_1342_)) as u8;
                if v_isSharedCheck_1389_ == 0 {
                    v___x_1348_ = v_m_1342_;
                    v_isShared_1349_ = v_isSharedCheck_1389_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1346_);
                    crate::leanh::lean_inc(v_size_1345_);
                    crate::leanh::lean_dec(v_m_1342_);
                    v___x_1348_ = crate::leanh::lean_box(0);
                    v_isShared_1349_ = v_isSharedCheck_1389_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1350_ = lean_array_get_size(v_buckets_1346_);
                v___x_1351_ = l_Lean_instHashableLevelMVarId_hash(v_a_1343_);
                v___x_1352_ = 32u64;
                v___x_1353_ = lean_uint64_shift_right(v___x_1351_, v___x_1352_);
                v_fold_1354_ = lean_uint64_xor(v___x_1351_, v___x_1353_);
                v___x_1355_ = 16u64;
                v___x_1356_ = lean_uint64_shift_right(v_fold_1354_, v___x_1355_);
                v___x_1357_ = lean_uint64_xor(v_fold_1354_, v___x_1356_);
                v___x_1358_ = lean_uint64_to_usize(v___x_1357_);
                v___x_1359_ = lean_usize_of_nat(v___x_1350_);
                v___x_1360_ = 1usize;
                v___x_1361_ = lean_usize_sub(v___x_1359_, v___x_1360_);
                v___x_1362_ = lean_usize_land(v___x_1358_, v___x_1361_);
                v_bkt_1363_ = lean_array_uget_borrowed(v_buckets_1346_, v___x_1362_);
                v___x_1364_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_1343_, v_bkt_1363_);
                if v___x_1364_ == 0 {
                    v___x_1365_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1366_ = lean_nat_add(v_size_1345_, v___x_1365_);
                    crate::leanh::lean_dec(v_size_1345_);
                    crate::leanh::lean_inc(v_bkt_1363_);
                    v___x_1367_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1367_, 0, v_a_1343_);
                    crate::leanh::lean_ctor_set(v___x_1367_, 1, v_b_1344_);
                    crate::leanh::lean_ctor_set(v___x_1367_, 2, v_bkt_1363_);
                    v_buckets_x27_1368_ =
                        lean_array_uset(v_buckets_1346_, v___x_1362_, v___x_1367_);
                    v___x_1369_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1370_ = lean_nat_mul(v_size_x27_1366_, v___x_1369_);
                    v___x_1371_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1372_ = lean_nat_div(v___x_1370_, v___x_1371_);
                    crate::leanh::lean_dec(v___x_1370_);
                    v___x_1373_ = lean_array_get_size(v_buckets_x27_1368_);
                    v___x_1374_ = lean_nat_dec_le(v___x_1372_, v___x_1373_);
                    crate::leanh::lean_dec(v___x_1372_);
                    if v___x_1374_ == 0 {
                        v_val_1375_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_buckets_x27_1368_);
                        if v_isShared_1349_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1348_, 1, v_val_1375_);
                            crate::leanh::lean_ctor_set(v___x_1348_, 0, v_size_x27_1366_);
                            v___x_1377_ = v___x_1348_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1378_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1378_,
                                0,
                                v_size_x27_1366_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_val_1375_);
                            v___x_1377_ = v_reuseFailAlloc_1378_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1349_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1348_, 1, v_buckets_x27_1368_);
                            crate::leanh::lean_ctor_set(v___x_1348_, 0, v_size_x27_1366_);
                            v___x_1380_ = v___x_1348_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1381_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1381_,
                                0,
                                v_size_x27_1366_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1381_,
                                1,
                                v_buckets_x27_1368_,
                            );
                            v___x_1380_ = v_reuseFailAlloc_1381_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1363_);
                    v___x_1382_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1383_ =
                        lean_array_uset(v_buckets_1346_, v___x_1362_, v___x_1382_);
                    v___x_1384_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_1343_, v_b_1344_, v_bkt_1363_);
                    v___x_1385_ = lean_array_uset(v_buckets_x27_1383_, v___x_1362_, v___x_1384_);
                    if v_isShared_1349_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1348_, 1, v___x_1385_);
                        v___x_1387_ = v___x_1348_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1388_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_size_1345_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1385_);
                        v___x_1387_ = v_reuseFailAlloc_1388_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1377_;
            }
            3 => {
                return v___x_1380_;
            }
            4 => {
                return v___x_1387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(
    mut v_a_1390_: *mut crate::leanh::LeanObject,
    mut v_x_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1391_) == 0 {
                    v___x_1392_ = crate::leanh::lean_box(0);
                    return v___x_1392_;
                } else {
                    v_key_1393_ = crate::leanh::lean_ctor_get(v_x_1391_, 0);
                    v_value_1394_ = crate::leanh::lean_ctor_get(v_x_1391_, 1);
                    v_tail_1395_ = crate::leanh::lean_ctor_get(v_x_1391_, 2);
                    v___x_1396_ = l_Lean_instBEqLevelMVarId_beq(v_key_1393_, v_a_1390_);
                    if v___x_1396_ == 0 {
                        v_x_1391_ = v_tail_1395_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1394_);
                        v___x_1398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1398_, 0, v_value_1394_);
                        return v___x_1398_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg___boxed(
    mut v_a_1399_: *mut crate::leanh::LeanObject,
    mut v_x_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_1399_, v_x_1400_);
    crate::leanh::lean_dec(v_x_1400_);
    crate::leanh::lean_dec(v_a_1399_);
    return v_res_1401_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(
    mut v_m_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: u64 = 0;
    let mut v___x_1407_: u64 = 0;
    let mut v___x_1408_: u64 = 0;
    let mut v_fold_1409_: u64 = 0;
    let mut v___x_1410_: u64 = 0;
    let mut v___x_1411_: u64 = 0;
    let mut v___x_1412_: u64 = 0;
    let mut v___x_1413_: usize = 0;
    let mut v___x_1414_: usize = 0;
    let mut v___x_1415_: usize = 0;
    let mut v___x_1416_: usize = 0;
    let mut v___x_1417_: usize = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1404_ = crate::leanh::lean_ctor_get(v_m_1402_, 1);
    v___x_1405_ = lean_array_get_size(v_buckets_1404_);
    v___x_1406_ = l_Lean_instHashableLevelMVarId_hash(v_a_1403_);
    v___x_1407_ = 32u64;
    v___x_1408_ = lean_uint64_shift_right(v___x_1406_, v___x_1407_);
    v_fold_1409_ = lean_uint64_xor(v___x_1406_, v___x_1408_);
    v___x_1410_ = 16u64;
    v___x_1411_ = lean_uint64_shift_right(v_fold_1409_, v___x_1410_);
    v___x_1412_ = lean_uint64_xor(v_fold_1409_, v___x_1411_);
    v___x_1413_ = lean_uint64_to_usize(v___x_1412_);
    v___x_1414_ = lean_usize_of_nat(v___x_1405_);
    v___x_1415_ = 1usize;
    v___x_1416_ = lean_usize_sub(v___x_1414_, v___x_1415_);
    v___x_1417_ = lean_usize_land(v___x_1413_, v___x_1416_);
    v___x_1418_ = lean_array_uget_borrowed(v_buckets_1404_, v___x_1417_);
    v___x_1419_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_1403_, v___x_1418_);
    return v___x_1419_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(
    mut v_m_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_1420_, v_a_1421_);
    crate::leanh::lean_dec(v_a_1421_);
    crate::leanh::lean_dec_ref(v_m_1420_);
    return v_res_1422_;
}
pub unsafe fn l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(
    mut v_u_1426_: *mut crate::leanh::LeanObject,
    mut v_a_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_abstractLevels_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1447_: u8 = 0;
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1458_: u8 = 0;
    let mut v_a_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1469_: u8 = 0;
    let mut v___y_1471_: u8 = 0;
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: usize = 0;
    let mut v___x_1481_: usize = 0;
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: u8 = 0;
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v_a_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___y_1499_: u8 = 0;
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: usize = 0;
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: usize = 0;
    let mut v___x_1513_: u8 = 0;
    let mut v_isSharedCheck_1514_: u8 = 0;
    let mut v_a_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1535_: u8 = 0;
    let mut v_unused_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_abstractLevels_1428_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1427_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                if v_abstractLevels_1428_ == 0 {
                    v___x_1429_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v_u_1426_);
                    crate::leanh::lean_ctor_set(v___x_1429_, 1, v_a_1427_);
                    return v___x_1429_;
                } else {
                    v_ngen_1430_ = crate::leanh::lean_ctor_get(v_a_1427_, 0);
                    v_lctx_1431_ = crate::leanh::lean_ctor_get(v_a_1427_, 1);
                    v_mctx_1432_ = crate::leanh::lean_ctor_get(v_a_1427_, 2);
                    v_nextParamIdx_1433_ = crate::leanh::lean_ctor_get(v_a_1427_, 3);
                    v_paramNames_1434_ = crate::leanh::lean_ctor_get(v_a_1427_, 4);
                    v_fvars_1435_ = crate::leanh::lean_ctor_get(v_a_1427_, 5);
                    v_mvars_1436_ = crate::leanh::lean_ctor_get(v_a_1427_, 6);
                    v_lmap_1437_ = crate::leanh::lean_ctor_get(v_a_1427_, 7);
                    v_emap_1438_ = crate::leanh::lean_ctor_get(v_a_1427_, 8);
                    v___x_1439_ = l_Lean_Level_hasMVar(v_u_1426_);
                    if v___x_1439_ == 0 {
                        v___x_1440_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1440_, 0, v_u_1426_);
                        crate::leanh::lean_ctor_set(v___x_1440_, 1, v_a_1427_);
                        return v___x_1440_;
                    } else {
                        match crate::leanh::lean_obj_tag(v_u_1426_) {
                            1 => {
                                v_a_1441_ = crate::leanh::lean_ctor_get(v_u_1426_, 0);
                                crate::leanh::lean_inc(v_a_1441_);
                                v___x_1442_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1441_, v_a_1427_);
                                v_fst_1443_ = crate::leanh::lean_ctor_get(v___x_1442_, 0);
                                v_snd_1444_ = crate::leanh::lean_ctor_get(v___x_1442_, 1);
                                v_isSharedCheck_1458_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1442_)) as u8;
                                if v_isSharedCheck_1458_ == 0 {
                                    v___x_1446_ = v___x_1442_;
                                    v_isShared_1447_ = v_isSharedCheck_1458_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_1444_);
                                    crate::leanh::lean_inc(v_fst_1443_);
                                    crate::leanh::lean_dec(v___x_1442_);
                                    v___x_1446_ = crate::leanh::lean_box(0);
                                    v_isShared_1447_ = v_isSharedCheck_1458_;
                                    state = 1;
                                    continue;
                                }
                            }
                            2 => {
                                v_a_1459_ = crate::leanh::lean_ctor_get(v_u_1426_, 0);
                                v_a_1460_ = crate::leanh::lean_ctor_get(v_u_1426_, 1);
                                crate::leanh::lean_inc(v_a_1459_);
                                v___x_1461_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1459_, v_a_1427_);
                                v_fst_1462_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
                                crate::leanh::lean_inc(v_fst_1462_);
                                v_snd_1463_ = crate::leanh::lean_ctor_get(v___x_1461_, 1);
                                crate::leanh::lean_inc(v_snd_1463_);
                                crate::leanh::lean_dec_ref(v___x_1461_);
                                crate::leanh::lean_inc(v_a_1460_);
                                v___x_1464_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1460_, v_snd_1463_);
                                v_fst_1465_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                                v_snd_1466_ = crate::leanh::lean_ctor_get(v___x_1464_, 1);
                                v_isSharedCheck_1486_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1464_)) as u8;
                                if v_isSharedCheck_1486_ == 0 {
                                    v___x_1468_ = v___x_1464_;
                                    v_isShared_1469_ = v_isSharedCheck_1486_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_1466_);
                                    crate::leanh::lean_inc(v_fst_1465_);
                                    crate::leanh::lean_dec(v___x_1464_);
                                    v___x_1468_ = crate::leanh::lean_box(0);
                                    v_isShared_1469_ = v_isSharedCheck_1486_;
                                    state = 4;
                                    continue;
                                }
                            }
                            3 => {
                                v_a_1487_ = crate::leanh::lean_ctor_get(v_u_1426_, 0);
                                v_a_1488_ = crate::leanh::lean_ctor_get(v_u_1426_, 1);
                                crate::leanh::lean_inc(v_a_1487_);
                                v___x_1489_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1487_, v_a_1427_);
                                v_fst_1490_ = crate::leanh::lean_ctor_get(v___x_1489_, 0);
                                crate::leanh::lean_inc(v_fst_1490_);
                                v_snd_1491_ = crate::leanh::lean_ctor_get(v___x_1489_, 1);
                                crate::leanh::lean_inc(v_snd_1491_);
                                crate::leanh::lean_dec_ref(v___x_1489_);
                                crate::leanh::lean_inc(v_a_1488_);
                                v___x_1492_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1488_, v_snd_1491_);
                                v_fst_1493_ = crate::leanh::lean_ctor_get(v___x_1492_, 0);
                                v_snd_1494_ = crate::leanh::lean_ctor_get(v___x_1492_, 1);
                                v_isSharedCheck_1514_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1492_)) as u8;
                                if v_isSharedCheck_1514_ == 0 {
                                    v___x_1496_ = v___x_1492_;
                                    v_isShared_1497_ = v_isSharedCheck_1514_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_1494_);
                                    crate::leanh::lean_inc(v_fst_1493_);
                                    crate::leanh::lean_dec(v___x_1492_);
                                    v___x_1496_ = crate::leanh::lean_box(0);
                                    v_isShared_1497_ = v_isSharedCheck_1514_;
                                    state = 8;
                                    continue;
                                }
                            }
                            5 => {
                                v_a_1515_ = crate::leanh::lean_ctor_get(v_u_1426_, 0);
                                v_depth_1516_ = crate::leanh::lean_ctor_get(v_mctx_1432_, 0);
                                crate::leanh::lean_inc(v_a_1515_);
                                v___x_1517_ =
                                    l_Lean_MetavarContext_getLevelDepth(v_mctx_1432_, v_a_1515_);
                                v___x_1518_ = lean_nat_dec_eq(v___x_1517_, v_depth_1516_);
                                crate::leanh::lean_dec(v___x_1517_);
                                if v___x_1518_ == 0 {
                                    v___x_1519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1519_, 0, v_u_1426_);
                                    crate::leanh::lean_ctor_set(v___x_1519_, 1, v_a_1427_);
                                    return v___x_1519_;
                                } else {
                                    crate::leanh::lean_inc(v_a_1515_);
                                    crate::leanh::lean_dec_ref_known(v_u_1426_, 1);
                                    v___x_1520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_lmap_1437_, v_a_1515_);
                                    if crate::leanh::lean_obj_tag(v___x_1520_) == 0 {
                                        crate::leanh::lean_inc_ref(v_emap_1438_);
                                        crate::leanh::lean_inc_ref(v_lmap_1437_);
                                        crate::leanh::lean_inc_ref(v_mvars_1436_);
                                        crate::leanh::lean_inc_ref(v_fvars_1435_);
                                        crate::leanh::lean_inc_ref(v_paramNames_1434_);
                                        crate::leanh::lean_inc(v_nextParamIdx_1433_);
                                        crate::leanh::lean_inc_ref(v_mctx_1432_);
                                        crate::leanh::lean_inc_ref(v_lctx_1431_);
                                        crate::leanh::lean_inc_ref(v_ngen_1430_);
                                        v_isSharedCheck_1535_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_1427_)) as u8;
                                        if v_isSharedCheck_1535_ == 0 {
                                            v_unused_1536_ =
                                                crate::leanh::lean_ctor_get(v_a_1427_, 8);
                                            crate::leanh::lean_dec(v_unused_1536_);
                                            v_unused_1537_ =
                                                crate::leanh::lean_ctor_get(v_a_1427_, 7);
                                            crate::leanh::lean_dec(v_unused_1537_);
                                            v_unused_1538_ =
                                                crate::leanh::lean_ctor_get(v_a_1427_, 6);
                                            crate::leanh::lean_dec(v_unused_1538_);
                                            v_unused_1539_ =
                                                crate::leanh::lean_ctor_get(v_a_1427_, 5);
                                            crate::leanh::lean_dec(v_unused_1539_);
                                            v_unused_1540_ =
                                                crate::leanh::lean_ctor_get(v_a_1427_, 4);
                                            crate::leanh::lean_dec(v_unused_1540_);
                                            v_unused_1541_ =
                                                crate::leanh::lean_ctor_get(v_a_1427_, 3);
                                            crate::leanh::lean_dec(v_unused_1541_);
                                            v_unused_1542_ =
                                                crate::leanh::lean_ctor_get(v_a_1427_, 2);
                                            crate::leanh::lean_dec(v_unused_1542_);
                                            v_unused_1543_ =
                                                crate::leanh::lean_ctor_get(v_a_1427_, 1);
                                            crate::leanh::lean_dec(v_unused_1543_);
                                            v_unused_1544_ =
                                                crate::leanh::lean_ctor_get(v_a_1427_, 0);
                                            crate::leanh::lean_dec(v_unused_1544_);
                                            v___x_1522_ = v_a_1427_;
                                            v_isShared_1523_ = v_isSharedCheck_1535_;
                                            state = 12;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_1427_);
                                            v___x_1522_ = crate::leanh::lean_box(0);
                                            v_isShared_1523_ = v_isSharedCheck_1535_;
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1515_);
                                        v_val_1545_ = crate::leanh::lean_ctor_get(v___x_1520_, 0);
                                        crate::leanh::lean_inc(v_val_1545_);
                                        crate::leanh::lean_dec_ref_known(v___x_1520_, 1);
                                        v___x_1546_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1546_, 0, v_val_1545_);
                                        crate::leanh::lean_ctor_set(v___x_1546_, 1, v_a_1427_);
                                        return v___x_1546_;
                                    }
                                }
                            }
                            _ => {
                                v___x_1547_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1547_, 0, v_u_1426_);
                                crate::leanh::lean_ctor_set(v___x_1547_, 1, v_a_1427_);
                                return v___x_1547_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1448_ = lean_ptr_addr(v_a_1441_);
                v___x_1449_ = lean_ptr_addr(v_fst_1443_);
                v___x_1450_ = lean_usize_dec_eq(v___x_1448_, v___x_1449_);
                if v___x_1450_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_u_1426_, 1);
                    v___x_1451_ = l_Lean_Level_succ___override(v_fst_1443_);
                    if v_isShared_1447_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1446_, 0, v___x_1451_);
                        v___x_1453_ = v___x_1446_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_snd_1444_);
                        v___x_1453_ = v_reuseFailAlloc_1454_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1443_);
                    if v_isShared_1447_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1446_, 0, v_u_1426_);
                        v___x_1456_ = v___x_1446_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1457_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_u_1426_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_snd_1444_);
                        v___x_1456_ = v_reuseFailAlloc_1457_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1453_;
            }
            3 => {
                return v___x_1456_;
            }
            4 => {
                v___x_1480_ = lean_ptr_addr(v_a_1459_);
                v___x_1481_ = lean_ptr_addr(v_fst_1462_);
                v___x_1482_ = lean_usize_dec_eq(v___x_1480_, v___x_1481_);
                if v___x_1482_ == 0 {
                    v___y_1471_ = v___x_1482_;
                    state = 5;
                    continue;
                } else {
                    v___x_1483_ = lean_ptr_addr(v_a_1460_);
                    v___x_1484_ = lean_ptr_addr(v_fst_1465_);
                    v___x_1485_ = lean_usize_dec_eq(v___x_1483_, v___x_1484_);
                    v___y_1471_ = v___x_1485_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_1471_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_u_1426_, 2);
                    v___x_1472_ = l_Lean_mkLevelMax_x27(v_fst_1462_, v_fst_1465_);
                    if v_isShared_1469_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1468_, 0, v___x_1472_);
                        v___x_1474_ = v___x_1468_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_snd_1466_);
                        v___x_1474_ = v_reuseFailAlloc_1475_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_1476_ = l_Lean_simpLevelMax_x27(v_fst_1462_, v_fst_1465_, v_u_1426_);
                    crate::leanh::lean_dec_ref_known(v_u_1426_, 2);
                    crate::leanh::lean_dec(v_fst_1465_);
                    crate::leanh::lean_dec(v_fst_1462_);
                    if v_isShared_1469_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1468_, 0, v___x_1476_);
                        v___x_1478_ = v___x_1468_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1479_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_snd_1466_);
                        v___x_1478_ = v_reuseFailAlloc_1479_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1474_;
            }
            7 => {
                return v___x_1478_;
            }
            8 => {
                v___x_1508_ = lean_ptr_addr(v_a_1487_);
                v___x_1509_ = lean_ptr_addr(v_fst_1490_);
                v___x_1510_ = lean_usize_dec_eq(v___x_1508_, v___x_1509_);
                if v___x_1510_ == 0 {
                    v___y_1499_ = v___x_1510_;
                    state = 9;
                    continue;
                } else {
                    v___x_1511_ = lean_ptr_addr(v_a_1488_);
                    v___x_1512_ = lean_ptr_addr(v_fst_1493_);
                    v___x_1513_ = lean_usize_dec_eq(v___x_1511_, v___x_1512_);
                    v___y_1499_ = v___x_1513_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v___y_1499_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_u_1426_, 2);
                    v___x_1500_ = l_Lean_mkLevelIMax_x27(v_fst_1490_, v_fst_1493_);
                    if v_isShared_1497_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1496_, 0, v___x_1500_);
                        v___x_1502_ = v___x_1496_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1503_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_snd_1494_);
                        v___x_1502_ = v_reuseFailAlloc_1503_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_1504_ = l_Lean_simpLevelIMax_x27(v_fst_1490_, v_fst_1493_, v_u_1426_);
                    crate::leanh::lean_dec_ref_known(v_u_1426_, 2);
                    if v_isShared_1497_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1496_, 0, v___x_1504_);
                        v___x_1506_ = v___x_1496_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1507_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_snd_1494_);
                        v___x_1506_ = v_reuseFailAlloc_1507_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_1502_;
            }
            11 => {
                return v___x_1506_;
            }
            12 => {
                v___x_1524_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1;
                crate::leanh::lean_inc(v_nextParamIdx_1433_);
                v___x_1525_ = l_Lean_Name_num___override(v___x_1524_, v_nextParamIdx_1433_);
                crate::leanh::lean_inc(v___x_1525_);
                v___x_1526_ = l_Lean_mkLevelParam(v___x_1525_);
                v___x_1527_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1528_ = lean_nat_add(v_nextParamIdx_1433_, v___x_1527_);
                crate::leanh::lean_dec(v_nextParamIdx_1433_);
                v___x_1529_ = lean_array_push(v_paramNames_1434_, v___x_1525_);
                crate::leanh::lean_inc(v___x_1526_);
                v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_lmap_1437_, v_a_1515_, v___x_1526_);
                if v_isShared_1523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1522_, 7, v___x_1530_);
                    crate::leanh::lean_ctor_set(v___x_1522_, 4, v___x_1529_);
                    crate::leanh::lean_ctor_set(v___x_1522_, 3, v___x_1528_);
                    v___x_1532_ = v___x_1522_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1534_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_ngen_1430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_lctx_1431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_mctx_1432_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 3, v___x_1528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 4, v___x_1529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 5, v_fvars_1435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 6, v_mvars_1436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 7, v___x_1530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 8, v_emap_1438_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1534_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1428_,
                    );
                    v___x_1532_ = v_reuseFailAlloc_1534_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1533_, 0, v___x_1526_);
                crate::leanh::lean_ctor_set(v___x_1533_, 1, v___x_1532_);
                return v___x_1533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(
    mut v_00_u03b2_1548_: *mut crate::leanh::LeanObject,
    mut v_m_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_1549_, v_a_1550_);
    return v___x_1551_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(
    mut v_00_u03b2_1552_: *mut crate::leanh::LeanObject,
    mut v_m_1553_: *mut crate::leanh::LeanObject,
    mut v_a_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(v_00_u03b2_1552_, v_m_1553_, v_a_1554_);
    crate::leanh::lean_dec(v_a_1554_);
    crate::leanh::lean_dec_ref(v_m_1553_);
    return v_res_1555_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(
    mut v_00_u03b2_1556_: *mut crate::leanh::LeanObject,
    mut v_m_1557_: *mut crate::leanh::LeanObject,
    mut v_a_1558_: *mut crate::leanh::LeanObject,
    mut v_b_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_1557_, v_a_1558_, v_b_1559_);
    return v___x_1560_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(
    mut v_00_u03b2_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_x_1563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_1562_, v_x_1563_);
    return v___x_1564_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
    mut v_x_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(v_00_u03b2_1565_, v_a_1566_, v_x_1567_);
    crate::leanh::lean_dec(v_x_1567_);
    crate::leanh::lean_dec(v_a_1566_);
    return v_res_1568_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(
    mut v_00_u03b2_1569_: *mut crate::leanh::LeanObject,
    mut v_a_1570_: *mut crate::leanh::LeanObject,
    mut v_x_1571_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1572_: u8 = 0;
    v___x_1572_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_1570_, v_x_1571_);
    return v___x_1572_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(
    mut v_00_u03b2_1573_: *mut crate::leanh::LeanObject,
    mut v_a_1574_: *mut crate::leanh::LeanObject,
    mut v_x_1575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1576_: u8 = 0;
    let mut v_r_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(v_00_u03b2_1573_, v_a_1574_, v_x_1575_);
    crate::leanh::lean_dec(v_x_1575_);
    crate::leanh::lean_dec(v_a_1574_);
    v_r_1577_ = crate::leanh::lean_box((v_res_1576_) as usize);
    return v_r_1577_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3(
    mut v_00_u03b2_1578_: *mut crate::leanh::LeanObject,
    mut v_data_1579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_data_1579_);
    return v___x_1580_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4(
    mut v_00_u03b2_1581_: *mut crate::leanh::LeanObject,
    mut v_a_1582_: *mut crate::leanh::LeanObject,
    mut v_b_1583_: *mut crate::leanh::LeanObject,
    mut v_x_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_1582_, v_b_1583_, v_x_1584_);
    return v___x_1585_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1586_: *mut crate::leanh::LeanObject,
    mut v_i_1587_: *mut crate::leanh::LeanObject,
    mut v_source_1588_: *mut crate::leanh::LeanObject,
    mut v_target_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1590_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v_i_1587_, v_source_1588_, v_target_1589_);
    return v___x_1590_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1591_: *mut crate::leanh::LeanObject,
    mut v_x_1592_: *mut crate::leanh::LeanObject,
    mut v_x_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1592_, v_x_1593_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(
    mut v_e_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1597_: u8 = 0;
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1608_: u8 = 0;
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1617_: u8 = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1597_ = l_Lean_Expr_hasMVar(v_e_1595_);
                if v___x_1597_ == 0 {
                    v___x_1598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1598_, 0, v_e_1595_);
                    crate::leanh::lean_ctor_set(v___x_1598_, 1, v___y_1596_);
                    return v___x_1598_;
                } else {
                    v_ngen_1599_ = crate::leanh::lean_ctor_get(v___y_1596_, 0);
                    v_lctx_1600_ = crate::leanh::lean_ctor_get(v___y_1596_, 1);
                    v_mctx_1601_ = crate::leanh::lean_ctor_get(v___y_1596_, 2);
                    v_nextParamIdx_1602_ = crate::leanh::lean_ctor_get(v___y_1596_, 3);
                    v_paramNames_1603_ = crate::leanh::lean_ctor_get(v___y_1596_, 4);
                    v_fvars_1604_ = crate::leanh::lean_ctor_get(v___y_1596_, 5);
                    v_mvars_1605_ = crate::leanh::lean_ctor_get(v___y_1596_, 6);
                    v_lmap_1606_ = crate::leanh::lean_ctor_get(v___y_1596_, 7);
                    v_emap_1607_ = crate::leanh::lean_ctor_get(v___y_1596_, 8);
                    v_abstractLevels_1608_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1596_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                    );
                    v_isSharedCheck_1625_ = (!crate::leanh::lean_is_exclusive(v___y_1596_)) as u8;
                    if v_isSharedCheck_1625_ == 0 {
                        v___x_1610_ = v___y_1596_;
                        v_isShared_1611_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_emap_1607_);
                        crate::leanh::lean_inc(v_lmap_1606_);
                        crate::leanh::lean_inc(v_mvars_1605_);
                        crate::leanh::lean_inc(v_fvars_1604_);
                        crate::leanh::lean_inc(v_paramNames_1603_);
                        crate::leanh::lean_inc(v_nextParamIdx_1602_);
                        crate::leanh::lean_inc(v_mctx_1601_);
                        crate::leanh::lean_inc(v_lctx_1600_);
                        crate::leanh::lean_inc(v_ngen_1599_);
                        crate::leanh::lean_dec(v___y_1596_);
                        v___x_1610_ = crate::leanh::lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1612_ = l_Lean_instantiateMVarsCore(v_mctx_1601_, v_e_1595_);
                v_fst_1613_ = crate::leanh::lean_ctor_get(v___x_1612_, 0);
                v_snd_1614_ = crate::leanh::lean_ctor_get(v___x_1612_, 1);
                v_isSharedCheck_1624_ = (!crate::leanh::lean_is_exclusive(v___x_1612_)) as u8;
                if v_isSharedCheck_1624_ == 0 {
                    v___x_1616_ = v___x_1612_;
                    v_isShared_1617_ = v_isSharedCheck_1624_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1614_);
                    crate::leanh::lean_inc(v_fst_1613_);
                    crate::leanh::lean_dec(v___x_1612_);
                    v___x_1616_ = crate::leanh::lean_box(0);
                    v_isShared_1617_ = v_isSharedCheck_1624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1611_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1610_, 2, v_snd_1614_);
                    v___x_1619_ = v___x_1610_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1623_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_ngen_1599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_lctx_1600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_snd_1614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_nextParamIdx_1602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 4, v_paramNames_1603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 5, v_fvars_1604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 6, v_mvars_1605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 7, v_lmap_1606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 8, v_emap_1607_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1623_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1608_,
                    );
                    v___x_1619_ = v_reuseFailAlloc_1623_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1616_, 1, v___x_1619_);
                    v___x_1621_ = v___x_1616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1622_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_fst_1613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1619_);
                    v___x_1621_ = v_reuseFailAlloc_1622_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(
    mut v_a_1626_: *mut crate::leanh::LeanObject,
    mut v_x_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1627_) == 0 {
                    v___x_1628_ = crate::leanh::lean_box(0);
                    return v___x_1628_;
                } else {
                    v_key_1629_ = crate::leanh::lean_ctor_get(v_x_1627_, 0);
                    v_value_1630_ = crate::leanh::lean_ctor_get(v_x_1627_, 1);
                    v_tail_1631_ = crate::leanh::lean_ctor_get(v_x_1627_, 2);
                    v___x_1632_ = l_Lean_instBEqMVarId_beq(v_key_1629_, v_a_1626_);
                    if v___x_1632_ == 0 {
                        v_x_1627_ = v_tail_1631_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1630_);
                        v___x_1634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1634_, 0, v_value_1630_);
                        return v___x_1634_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_x_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_1635_, v_x_1636_);
    crate::leanh::lean_dec(v_x_1636_);
    crate::leanh::lean_dec(v_a_1635_);
    return v_res_1637_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(
    mut v_m_1638_: *mut crate::leanh::LeanObject,
    mut v_a_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u64 = 0;
    let mut v___x_1643_: u64 = 0;
    let mut v___x_1644_: u64 = 0;
    let mut v_fold_1645_: u64 = 0;
    let mut v___x_1646_: u64 = 0;
    let mut v___x_1647_: u64 = 0;
    let mut v___x_1648_: u64 = 0;
    let mut v___x_1649_: usize = 0;
    let mut v___x_1650_: usize = 0;
    let mut v___x_1651_: usize = 0;
    let mut v___x_1652_: usize = 0;
    let mut v___x_1653_: usize = 0;
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1640_ = crate::leanh::lean_ctor_get(v_m_1638_, 1);
    v___x_1641_ = lean_array_get_size(v_buckets_1640_);
    v___x_1642_ = l_Lean_instHashableMVarId_hash(v_a_1639_);
    v___x_1643_ = 32u64;
    v___x_1644_ = lean_uint64_shift_right(v___x_1642_, v___x_1643_);
    v_fold_1645_ = lean_uint64_xor(v___x_1642_, v___x_1644_);
    v___x_1646_ = 16u64;
    v___x_1647_ = lean_uint64_shift_right(v_fold_1645_, v___x_1646_);
    v___x_1648_ = lean_uint64_xor(v_fold_1645_, v___x_1647_);
    v___x_1649_ = lean_uint64_to_usize(v___x_1648_);
    v___x_1650_ = lean_usize_of_nat(v___x_1641_);
    v___x_1651_ = 1usize;
    v___x_1652_ = lean_usize_sub(v___x_1650_, v___x_1651_);
    v___x_1653_ = lean_usize_land(v___x_1649_, v___x_1652_);
    v___x_1654_ = lean_array_uget_borrowed(v_buckets_1640_, v___x_1653_);
    v___x_1655_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_1639_, v___x_1654_);
    return v___x_1655_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg___boxed(
    mut v_m_1656_: *mut crate::leanh::LeanObject,
    mut v_a_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_1656_, v_a_1657_);
    crate::leanh::lean_dec(v_a_1657_);
    crate::leanh::lean_dec_ref(v_m_1656_);
    return v_res_1658_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(
    mut v_a_1659_: *mut crate::leanh::LeanObject,
    mut v_x_1660_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1661_: u8 = 0;
    let mut v_key_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1660_) == 0 {
                    v___x_1661_ = 0;
                    return v___x_1661_;
                } else {
                    v_key_1662_ = crate::leanh::lean_ctor_get(v_x_1660_, 0);
                    v_tail_1663_ = crate::leanh::lean_ctor_get(v_x_1660_, 2);
                    v___x_1664_ = l_Lean_instBEqMVarId_beq(v_key_1662_, v_a_1659_);
                    if v___x_1664_ == 0 {
                        v_x_1660_ = v_tail_1663_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1664_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg___boxed(
    mut v_a_1666_: *mut crate::leanh::LeanObject,
    mut v_x_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1668_: u8 = 0;
    let mut v_r_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_1666_, v_x_1667_);
    crate::leanh::lean_dec(v_x_1667_);
    crate::leanh::lean_dec(v_a_1666_);
    v_r_1669_ = crate::leanh::lean_box((v_res_1668_) as usize);
    return v_r_1669_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(
    mut v_a_1670_: *mut crate::leanh::LeanObject,
    mut v_b_1671_: *mut crate::leanh::LeanObject,
    mut v_x_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1672_) == 0 {
                    crate::leanh::lean_dec(v_b_1671_);
                    crate::leanh::lean_dec(v_a_1670_);
                    return v_x_1672_;
                } else {
                    v_key_1673_ = crate::leanh::lean_ctor_get(v_x_1672_, 0);
                    v_value_1674_ = crate::leanh::lean_ctor_get(v_x_1672_, 1);
                    v_tail_1675_ = crate::leanh::lean_ctor_get(v_x_1672_, 2);
                    v_isSharedCheck_1687_ = (!crate::leanh::lean_is_exclusive(v_x_1672_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1677_ = v_x_1672_;
                        v_isShared_1678_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1675_);
                        crate::leanh::lean_inc(v_value_1674_);
                        crate::leanh::lean_inc(v_key_1673_);
                        crate::leanh::lean_dec(v_x_1672_);
                        v___x_1677_ = crate::leanh::lean_box(0);
                        v_isShared_1678_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1679_ = l_Lean_instBEqMVarId_beq(v_key_1673_, v_a_1670_);
                if v___x_1679_ == 0 {
                    v___x_1680_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_1670_, v_b_1671_, v_tail_1675_);
                    if v_isShared_1678_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1677_, 2, v___x_1680_);
                        v___x_1682_ = v___x_1677_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1683_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_key_1673_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_value_1674_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 2, v___x_1680_);
                        v___x_1682_ = v_reuseFailAlloc_1683_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1674_);
                    crate::leanh::lean_dec(v_key_1673_);
                    if v_isShared_1678_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1677_, 1, v_b_1671_);
                        crate::leanh::lean_ctor_set(v___x_1677_, 0, v_a_1670_);
                        v___x_1685_ = v___x_1677_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1686_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1670_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_b_1671_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_tail_1675_);
                        v___x_1685_ = v_reuseFailAlloc_1686_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1682_;
            }
            3 => {
                return v___x_1685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(
    mut v_x_1688_: *mut crate::leanh::LeanObject,
    mut v_x_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u64 = 0;
    let mut v___x_1698_: u64 = 0;
    let mut v___x_1699_: u64 = 0;
    let mut v_fold_1700_: u64 = 0;
    let mut v___x_1701_: u64 = 0;
    let mut v___x_1702_: u64 = 0;
    let mut v___x_1703_: u64 = 0;
    let mut v___x_1704_: usize = 0;
    let mut v___x_1705_: usize = 0;
    let mut v___x_1706_: usize = 0;
    let mut v___x_1707_: usize = 0;
    let mut v___x_1708_: usize = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1689_) == 0 {
                    return v_x_1688_;
                } else {
                    v_key_1690_ = crate::leanh::lean_ctor_get(v_x_1689_, 0);
                    v_value_1691_ = crate::leanh::lean_ctor_get(v_x_1689_, 1);
                    v_tail_1692_ = crate::leanh::lean_ctor_get(v_x_1689_, 2);
                    v_isSharedCheck_1715_ = (!crate::leanh::lean_is_exclusive(v_x_1689_)) as u8;
                    if v_isSharedCheck_1715_ == 0 {
                        v___x_1694_ = v_x_1689_;
                        v_isShared_1695_ = v_isSharedCheck_1715_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1692_);
                        crate::leanh::lean_inc(v_value_1691_);
                        crate::leanh::lean_inc(v_key_1690_);
                        crate::leanh::lean_dec(v_x_1689_);
                        v___x_1694_ = crate::leanh::lean_box(0);
                        v_isShared_1695_ = v_isSharedCheck_1715_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1696_ = lean_array_get_size(v_x_1688_);
                v___x_1697_ = l_Lean_instHashableMVarId_hash(v_key_1690_);
                v___x_1698_ = 32u64;
                v___x_1699_ = lean_uint64_shift_right(v___x_1697_, v___x_1698_);
                v_fold_1700_ = lean_uint64_xor(v___x_1697_, v___x_1699_);
                v___x_1701_ = 16u64;
                v___x_1702_ = lean_uint64_shift_right(v_fold_1700_, v___x_1701_);
                v___x_1703_ = lean_uint64_xor(v_fold_1700_, v___x_1702_);
                v___x_1704_ = lean_uint64_to_usize(v___x_1703_);
                v___x_1705_ = lean_usize_of_nat(v___x_1696_);
                v___x_1706_ = 1usize;
                v___x_1707_ = lean_usize_sub(v___x_1705_, v___x_1706_);
                v___x_1708_ = lean_usize_land(v___x_1704_, v___x_1707_);
                v___x_1709_ = lean_array_uget_borrowed(v_x_1688_, v___x_1708_);
                crate::leanh::lean_inc(v___x_1709_);
                if v_isShared_1695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1694_, 2, v___x_1709_);
                    v___x_1711_ = v___x_1694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_key_1690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_value_1691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 2, v___x_1709_);
                    v___x_1711_ = v_reuseFailAlloc_1714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1712_ = lean_array_uset(v_x_1688_, v___x_1708_, v___x_1711_);
                v_x_1688_ = v___x_1712_;
                v_x_1689_ = v_tail_1692_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(
    mut v_i_1716_: *mut crate::leanh::LeanObject,
    mut v_source_1717_: *mut crate::leanh::LeanObject,
    mut v_target_1718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v_es_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1719_ = lean_array_get_size(v_source_1717_);
                v___x_1720_ = lean_nat_dec_lt(v_i_1716_, v___x_1719_);
                if v___x_1720_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1717_);
                    crate::leanh::lean_dec(v_i_1716_);
                    return v_target_1718_;
                } else {
                    v_es_1721_ = lean_array_fget(v_source_1717_, v_i_1716_);
                    v___x_1722_ = crate::leanh::lean_box(0);
                    v_source_1723_ = lean_array_fset(v_source_1717_, v_i_1716_, v___x_1722_);
                    v_target_1724_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_target_1718_, v_es_1721_);
                    v___x_1725_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1726_ = lean_nat_add(v_i_1716_, v___x_1725_);
                    crate::leanh::lean_dec(v_i_1716_);
                    v_i_1716_ = v___x_1726_;
                    v_source_1717_ = v_source_1723_;
                    v_target_1718_ = v_target_1724_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(
    mut v_data_1728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1729_ = lean_array_get_size(v_data_1728_);
    v___x_1730_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1731_ = lean_nat_mul(v___x_1729_, v___x_1730_);
    v___x_1732_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1733_ = crate::leanh::lean_box(0);
    v___x_1734_ = lean_mk_array(v_nbuckets_1731_, v___x_1733_);
    v___x_1735_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v___x_1732_, v_data_1728_, v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(
    mut v_m_1736_: *mut crate::leanh::LeanObject,
    mut v_a_1737_: *mut crate::leanh::LeanObject,
    mut v_b_1738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1746_: u64 = 0;
    let mut v___x_1747_: u64 = 0;
    let mut v_fold_1748_: u64 = 0;
    let mut v___x_1749_: u64 = 0;
    let mut v___x_1750_: u64 = 0;
    let mut v___x_1751_: u64 = 0;
    let mut v___x_1752_: usize = 0;
    let mut v___x_1753_: usize = 0;
    let mut v___x_1754_: usize = 0;
    let mut v___x_1755_: usize = 0;
    let mut v___x_1756_: usize = 0;
    let mut v_bkt_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v_val_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1739_ = crate::leanh::lean_ctor_get(v_m_1736_, 0);
                v_buckets_1740_ = crate::leanh::lean_ctor_get(v_m_1736_, 1);
                v_isSharedCheck_1783_ = (!crate::leanh::lean_is_exclusive(v_m_1736_)) as u8;
                if v_isSharedCheck_1783_ == 0 {
                    v___x_1742_ = v_m_1736_;
                    v_isShared_1743_ = v_isSharedCheck_1783_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1740_);
                    crate::leanh::lean_inc(v_size_1739_);
                    crate::leanh::lean_dec(v_m_1736_);
                    v___x_1742_ = crate::leanh::lean_box(0);
                    v_isShared_1743_ = v_isSharedCheck_1783_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1744_ = lean_array_get_size(v_buckets_1740_);
                v___x_1745_ = l_Lean_instHashableMVarId_hash(v_a_1737_);
                v___x_1746_ = 32u64;
                v___x_1747_ = lean_uint64_shift_right(v___x_1745_, v___x_1746_);
                v_fold_1748_ = lean_uint64_xor(v___x_1745_, v___x_1747_);
                v___x_1749_ = 16u64;
                v___x_1750_ = lean_uint64_shift_right(v_fold_1748_, v___x_1749_);
                v___x_1751_ = lean_uint64_xor(v_fold_1748_, v___x_1750_);
                v___x_1752_ = lean_uint64_to_usize(v___x_1751_);
                v___x_1753_ = lean_usize_of_nat(v___x_1744_);
                v___x_1754_ = 1usize;
                v___x_1755_ = lean_usize_sub(v___x_1753_, v___x_1754_);
                v___x_1756_ = lean_usize_land(v___x_1752_, v___x_1755_);
                v_bkt_1757_ = lean_array_uget_borrowed(v_buckets_1740_, v___x_1756_);
                v___x_1758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_1737_, v_bkt_1757_);
                if v___x_1758_ == 0 {
                    v___x_1759_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1760_ = lean_nat_add(v_size_1739_, v___x_1759_);
                    crate::leanh::lean_dec(v_size_1739_);
                    crate::leanh::lean_inc(v_bkt_1757_);
                    v___x_1761_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1761_, 0, v_a_1737_);
                    crate::leanh::lean_ctor_set(v___x_1761_, 1, v_b_1738_);
                    crate::leanh::lean_ctor_set(v___x_1761_, 2, v_bkt_1757_);
                    v_buckets_x27_1762_ =
                        lean_array_uset(v_buckets_1740_, v___x_1756_, v___x_1761_);
                    v___x_1763_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1764_ = lean_nat_mul(v_size_x27_1760_, v___x_1763_);
                    v___x_1765_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1766_ = lean_nat_div(v___x_1764_, v___x_1765_);
                    crate::leanh::lean_dec(v___x_1764_);
                    v___x_1767_ = lean_array_get_size(v_buckets_x27_1762_);
                    v___x_1768_ = lean_nat_dec_le(v___x_1766_, v___x_1767_);
                    crate::leanh::lean_dec(v___x_1766_);
                    if v___x_1768_ == 0 {
                        v_val_1769_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_buckets_x27_1762_);
                        if v_isShared_1743_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1742_, 1, v_val_1769_);
                            crate::leanh::lean_ctor_set(v___x_1742_, 0, v_size_x27_1760_);
                            v___x_1771_ = v___x_1742_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1772_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1772_,
                                0,
                                v_size_x27_1760_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_val_1769_);
                            v___x_1771_ = v_reuseFailAlloc_1772_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1743_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1742_, 1, v_buckets_x27_1762_);
                            crate::leanh::lean_ctor_set(v___x_1742_, 0, v_size_x27_1760_);
                            v___x_1774_ = v___x_1742_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1775_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1775_,
                                0,
                                v_size_x27_1760_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1775_,
                                1,
                                v_buckets_x27_1762_,
                            );
                            v___x_1774_ = v_reuseFailAlloc_1775_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1757_);
                    v___x_1776_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1777_ =
                        lean_array_uset(v_buckets_1740_, v___x_1756_, v___x_1776_);
                    v___x_1778_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_1737_, v_b_1738_, v_bkt_1757_);
                    v___x_1779_ = lean_array_uset(v_buckets_x27_1777_, v___x_1756_, v___x_1778_);
                    if v_isShared_1743_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1742_, 1, v___x_1779_);
                        v___x_1781_ = v___x_1742_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_size_1739_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1779_);
                        v___x_1781_ = v_reuseFailAlloc_1782_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1771_;
            }
            3 => {
                return v___x_1774_;
            }
            4 => {
                return v___x_1781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(
    mut v_x_1784_: *mut crate::leanh::LeanObject,
    mut v_x_1785_: *mut crate::leanh::LeanObject,
    mut v___y_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1784_) == 0 {
                    v___x_1787_ = l_List_reverse___redArg(v_x_1785_);
                    v___x_1788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1788_, 0, v___x_1787_);
                    crate::leanh::lean_ctor_set(v___x_1788_, 1, v___y_1786_);
                    return v___x_1788_;
                } else {
                    v_head_1789_ = crate::leanh::lean_ctor_get(v_x_1784_, 0);
                    v_tail_1790_ = crate::leanh::lean_ctor_get(v_x_1784_, 1);
                    v_isSharedCheck_1801_ = (!crate::leanh::lean_is_exclusive(v_x_1784_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1792_ = v_x_1784_;
                        v_isShared_1793_ = v_isSharedCheck_1801_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1790_);
                        crate::leanh::lean_inc(v_head_1789_);
                        crate::leanh::lean_dec(v_x_1784_);
                        v___x_1792_ = crate::leanh::lean_box(0);
                        v_isShared_1793_ = v_isSharedCheck_1801_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1794_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_head_1789_, v___y_1786_);
                v_fst_1795_ = crate::leanh::lean_ctor_get(v___x_1794_, 0);
                crate::leanh::lean_inc(v_fst_1795_);
                v_snd_1796_ = crate::leanh::lean_ctor_get(v___x_1794_, 1);
                crate::leanh::lean_inc(v_snd_1796_);
                crate::leanh::lean_dec_ref(v___x_1794_);
                if v_isShared_1793_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1792_, 1, v_x_1785_);
                    crate::leanh::lean_ctor_set(v___x_1792_, 0, v_fst_1795_);
                    v___x_1798_ = v___x_1792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_fst_1795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_x_1785_);
                    v___x_1798_ = v_reuseFailAlloc_1800_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_1784_ = v_tail_1790_;
                v_x_1785_ = v___x_1798_;
                v___y_1786_ = v_snd_1796_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractMVars_abstractExprMVars(
    mut v_e_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1844_: u8 = 0;
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut v___x_1861_: u8 = 0;
    let mut v_fvars_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_val_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: usize = 0;
    let mut v___x_1878_: u8 = 0;
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_declName_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_fn_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___y_1917_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: usize = 0;
    let mut v___x_1926_: usize = 0;
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: usize = 0;
    let mut v___x_1929_: usize = 0;
    let mut v___x_1930_: u8 = 0;
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v_binderName_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1935_: u8 = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___y_1946_: u8 = 0;
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: usize = 0;
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: usize = 0;
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: u8 = 0;
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_binderName_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1969_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___y_1980_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: u8 = 0;
    let mut v___x_1996_: usize = 0;
    let mut v___x_1997_: usize = 0;
    let mut v___x_1998_: u8 = 0;
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_declName_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2004_: u8 = 0;
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___y_2018_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: usize = 0;
    let mut v___x_2024_: usize = 0;
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: usize = 0;
    let mut v___x_2034_: usize = 0;
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: usize = 0;
    let mut v___x_2037_: usize = 0;
    let mut v___x_2038_: u8 = 0;
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_data_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2047_: u8 = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: usize = 0;
    let mut v___x_2050_: u8 = 0;
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_typeName_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2067_: u8 = 0;
    let mut v___x_2068_: usize = 0;
    let mut v___x_2069_: usize = 0;
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2078_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1807_ = l_Lean_Expr_hasMVar(v_e_1805_);
                if v___x_1807_ == 0 {
                    v___x_1808_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1808_, 0, v_e_1805_);
                    crate::leanh::lean_ctor_set(v___x_1808_, 1, v_a_1806_);
                    return v___x_1808_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_1805_) {
                        2 => {
                            v_mvarId_1809_ = crate::leanh::lean_ctor_get(v_e_1805_, 0);
                            v_mctx_1810_ = crate::leanh::lean_ctor_get(v_a_1806_, 2);
                            v_emap_1811_ = crate::leanh::lean_ctor_get(v_a_1806_, 8);
                            crate::leanh::lean_inc(v_mvarId_1809_);
                            v___x_1812_ =
                                l_Lean_MetavarContext_getDecl(v_mctx_1810_, v_mvarId_1809_);
                            v_userName_1813_ = crate::leanh::lean_ctor_get(v___x_1812_, 0);
                            crate::leanh::lean_inc(v_userName_1813_);
                            v_type_1814_ = crate::leanh::lean_ctor_get(v___x_1812_, 2);
                            crate::leanh::lean_inc_ref(v_type_1814_);
                            v_depth_1815_ = crate::leanh::lean_ctor_get(v___x_1812_, 3);
                            crate::leanh::lean_inc(v_depth_1815_);
                            crate::leanh::lean_dec_ref(v___x_1812_);
                            v_depth_1816_ = crate::leanh::lean_ctor_get(v_mctx_1810_, 0);
                            v___x_1817_ = lean_nat_dec_eq(v_depth_1815_, v_depth_1816_);
                            crate::leanh::lean_dec(v_depth_1815_);
                            if v___x_1817_ == 0 {
                                crate::leanh::lean_dec_ref(v_type_1814_);
                                crate::leanh::lean_dec(v_userName_1813_);
                                v___x_1818_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1818_, 0, v_e_1805_);
                                crate::leanh::lean_ctor_set(v___x_1818_, 1, v_a_1806_);
                                return v___x_1818_;
                            } else {
                                crate::leanh::lean_inc(v_mvarId_1809_);
                                v___x_1819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_emap_1811_, v_mvarId_1809_);
                                if crate::leanh::lean_obj_tag(v___x_1819_) == 0 {
                                    v___x_1820_ = l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(v_type_1814_, v_a_1806_);
                                    v_fst_1821_ = crate::leanh::lean_ctor_get(v___x_1820_, 0);
                                    crate::leanh::lean_inc(v_fst_1821_);
                                    v_snd_1822_ = crate::leanh::lean_ctor_get(v___x_1820_, 1);
                                    crate::leanh::lean_inc(v_snd_1822_);
                                    crate::leanh::lean_dec_ref(v___x_1820_);
                                    v___x_1823_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                        v_fst_1821_,
                                        v_snd_1822_,
                                    );
                                    v_fst_1824_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
                                    crate::leanh::lean_inc(v_fst_1824_);
                                    v_snd_1825_ = crate::leanh::lean_ctor_get(v___x_1823_, 1);
                                    crate::leanh::lean_inc(v_snd_1825_);
                                    crate::leanh::lean_dec_ref(v___x_1823_);
                                    v___x_1826_ =
                                        l_Lean_Meta_AbstractMVars_mkFreshFVarId(v_snd_1825_);
                                    v_fst_1827_ = crate::leanh::lean_ctor_get(v___x_1826_, 0);
                                    v_snd_1828_ = crate::leanh::lean_ctor_get(v___x_1826_, 1);
                                    v_isSharedCheck_1866_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1826_)) as u8;
                                    if v_isSharedCheck_1866_ == 0 {
                                        v___x_1830_ = v___x_1826_;
                                        v_isShared_1831_ = v_isSharedCheck_1866_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_snd_1828_);
                                        crate::leanh::lean_inc(v_fst_1827_);
                                        crate::leanh::lean_dec(v___x_1826_);
                                        v___x_1830_ = crate::leanh::lean_box(0);
                                        v_isShared_1831_ = v_isSharedCheck_1866_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_type_1814_);
                                    crate::leanh::lean_dec(v_userName_1813_);
                                    crate::leanh::lean_dec_ref_known(v_e_1805_, 1);
                                    crate::leanh::lean_dec(v_mvarId_1809_);
                                    v_val_1867_ = crate::leanh::lean_ctor_get(v___x_1819_, 0);
                                    crate::leanh::lean_inc(v_val_1867_);
                                    crate::leanh::lean_dec_ref_known(v___x_1819_, 1);
                                    v___x_1868_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1868_, 0, v_val_1867_);
                                    crate::leanh::lean_ctor_set(v___x_1868_, 1, v_a_1806_);
                                    return v___x_1868_;
                                }
                            }
                        }
                        3 => {
                            v_u_1869_ = crate::leanh::lean_ctor_get(v_e_1805_, 0);
                            crate::leanh::lean_inc(v_u_1869_);
                            v___x_1870_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_u_1869_, v_a_1806_);
                            v_fst_1871_ = crate::leanh::lean_ctor_get(v___x_1870_, 0);
                            v_snd_1872_ = crate::leanh::lean_ctor_get(v___x_1870_, 1);
                            v_isSharedCheck_1886_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1870_)) as u8;
                            if v_isSharedCheck_1886_ == 0 {
                                v___x_1874_ = v___x_1870_;
                                v_isShared_1875_ = v_isSharedCheck_1886_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1872_);
                                crate::leanh::lean_inc(v_fst_1871_);
                                crate::leanh::lean_dec(v___x_1870_);
                                v___x_1874_ = crate::leanh::lean_box(0);
                                v_isShared_1875_ = v_isSharedCheck_1886_;
                                state = 6;
                                continue;
                            }
                        }
                        4 => {
                            v_declName_1887_ = crate::leanh::lean_ctor_get(v_e_1805_, 0);
                            v_us_1888_ = crate::leanh::lean_ctor_get(v_e_1805_, 1);
                            v___x_1889_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_us_1888_);
                            v___x_1890_ = l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(v_us_1888_, v___x_1889_, v_a_1806_);
                            v_fst_1891_ = crate::leanh::lean_ctor_get(v___x_1890_, 0);
                            v_snd_1892_ = crate::leanh::lean_ctor_get(v___x_1890_, 1);
                            v_isSharedCheck_1904_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1890_)) as u8;
                            if v_isSharedCheck_1904_ == 0 {
                                v___x_1894_ = v___x_1890_;
                                v_isShared_1895_ = v_isSharedCheck_1904_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1892_);
                                crate::leanh::lean_inc(v_fst_1891_);
                                crate::leanh::lean_dec(v___x_1890_);
                                v___x_1894_ = crate::leanh::lean_box(0);
                                v_isShared_1895_ = v_isSharedCheck_1904_;
                                state = 9;
                                continue;
                            }
                        }
                        5 => {
                            v_fn_1905_ = crate::leanh::lean_ctor_get(v_e_1805_, 0);
                            v_arg_1906_ = crate::leanh::lean_ctor_get(v_e_1805_, 1);
                            crate::leanh::lean_inc_ref(v_fn_1905_);
                            v___x_1907_ =
                                l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fn_1905_, v_a_1806_);
                            v_fst_1908_ = crate::leanh::lean_ctor_get(v___x_1907_, 0);
                            crate::leanh::lean_inc(v_fst_1908_);
                            v_snd_1909_ = crate::leanh::lean_ctor_get(v___x_1907_, 1);
                            crate::leanh::lean_inc(v_snd_1909_);
                            crate::leanh::lean_dec_ref(v___x_1907_);
                            crate::leanh::lean_inc_ref(v_arg_1906_);
                            v___x_1910_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_arg_1906_,
                                v_snd_1909_,
                            );
                            v_fst_1911_ = crate::leanh::lean_ctor_get(v___x_1910_, 0);
                            v_snd_1912_ = crate::leanh::lean_ctor_get(v___x_1910_, 1);
                            v_isSharedCheck_1931_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1910_)) as u8;
                            if v_isSharedCheck_1931_ == 0 {
                                v___x_1914_ = v___x_1910_;
                                v_isShared_1915_ = v_isSharedCheck_1931_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1912_);
                                crate::leanh::lean_inc(v_fst_1911_);
                                crate::leanh::lean_dec(v___x_1910_);
                                v___x_1914_ = crate::leanh::lean_box(0);
                                v_isShared_1915_ = v_isSharedCheck_1931_;
                                state = 12;
                                continue;
                            }
                        }
                        6 => {
                            v_binderName_1932_ = crate::leanh::lean_ctor_get(v_e_1805_, 0);
                            v_binderType_1933_ = crate::leanh::lean_ctor_get(v_e_1805_, 1);
                            v_body_1934_ = crate::leanh::lean_ctor_get(v_e_1805_, 2);
                            v_binderInfo_1935_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_1805_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_1933_);
                            v___x_1936_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_binderType_1933_,
                                v_a_1806_,
                            );
                            v_fst_1937_ = crate::leanh::lean_ctor_get(v___x_1936_, 0);
                            crate::leanh::lean_inc(v_fst_1937_);
                            v_snd_1938_ = crate::leanh::lean_ctor_get(v___x_1936_, 1);
                            crate::leanh::lean_inc(v_snd_1938_);
                            crate::leanh::lean_dec_ref(v___x_1936_);
                            crate::leanh::lean_inc_ref(v_body_1934_);
                            v___x_1939_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_body_1934_,
                                v_snd_1938_,
                            );
                            v_fst_1940_ = crate::leanh::lean_ctor_get(v___x_1939_, 0);
                            v_snd_1941_ = crate::leanh::lean_ctor_get(v___x_1939_, 1);
                            v_isSharedCheck_1965_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1939_)) as u8;
                            if v_isSharedCheck_1965_ == 0 {
                                v___x_1943_ = v___x_1939_;
                                v_isShared_1944_ = v_isSharedCheck_1965_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1941_);
                                crate::leanh::lean_inc(v_fst_1940_);
                                crate::leanh::lean_dec(v___x_1939_);
                                v___x_1943_ = crate::leanh::lean_box(0);
                                v_isShared_1944_ = v_isSharedCheck_1965_;
                                state = 16;
                                continue;
                            }
                        }
                        7 => {
                            v_binderName_1966_ = crate::leanh::lean_ctor_get(v_e_1805_, 0);
                            v_binderType_1967_ = crate::leanh::lean_ctor_get(v_e_1805_, 1);
                            v_body_1968_ = crate::leanh::lean_ctor_get(v_e_1805_, 2);
                            v_binderInfo_1969_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_1805_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_1967_);
                            v___x_1970_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_binderType_1967_,
                                v_a_1806_,
                            );
                            v_fst_1971_ = crate::leanh::lean_ctor_get(v___x_1970_, 0);
                            crate::leanh::lean_inc(v_fst_1971_);
                            v_snd_1972_ = crate::leanh::lean_ctor_get(v___x_1970_, 1);
                            crate::leanh::lean_inc(v_snd_1972_);
                            crate::leanh::lean_dec_ref(v___x_1970_);
                            crate::leanh::lean_inc_ref(v_body_1968_);
                            v___x_1973_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_body_1968_,
                                v_snd_1972_,
                            );
                            v_fst_1974_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                            v_snd_1975_ = crate::leanh::lean_ctor_get(v___x_1973_, 1);
                            v_isSharedCheck_1999_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1973_)) as u8;
                            if v_isSharedCheck_1999_ == 0 {
                                v___x_1977_ = v___x_1973_;
                                v_isShared_1978_ = v_isSharedCheck_1999_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1975_);
                                crate::leanh::lean_inc(v_fst_1974_);
                                crate::leanh::lean_dec(v___x_1973_);
                                v___x_1977_ = crate::leanh::lean_box(0);
                                v_isShared_1978_ = v_isSharedCheck_1999_;
                                state = 21;
                                continue;
                            }
                        }
                        8 => {
                            v_declName_2000_ = crate::leanh::lean_ctor_get(v_e_1805_, 0);
                            v_type_2001_ = crate::leanh::lean_ctor_get(v_e_1805_, 1);
                            v_value_2002_ = crate::leanh::lean_ctor_get(v_e_1805_, 2);
                            v_body_2003_ = crate::leanh::lean_ctor_get(v_e_1805_, 3);
                            v_nondep_2004_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_1805_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_type_2001_);
                            v___x_2005_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_type_2001_,
                                v_a_1806_,
                            );
                            v_fst_2006_ = crate::leanh::lean_ctor_get(v___x_2005_, 0);
                            crate::leanh::lean_inc(v_fst_2006_);
                            v_snd_2007_ = crate::leanh::lean_ctor_get(v___x_2005_, 1);
                            crate::leanh::lean_inc(v_snd_2007_);
                            crate::leanh::lean_dec_ref(v___x_2005_);
                            crate::leanh::lean_inc_ref(v_value_2002_);
                            v___x_2008_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_value_2002_,
                                v_snd_2007_,
                            );
                            v_fst_2009_ = crate::leanh::lean_ctor_get(v___x_2008_, 0);
                            crate::leanh::lean_inc(v_fst_2009_);
                            v_snd_2010_ = crate::leanh::lean_ctor_get(v___x_2008_, 1);
                            crate::leanh::lean_inc(v_snd_2010_);
                            crate::leanh::lean_dec_ref(v___x_2008_);
                            crate::leanh::lean_inc_ref(v_body_2003_);
                            v___x_2011_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_body_2003_,
                                v_snd_2010_,
                            );
                            v_fst_2012_ = crate::leanh::lean_ctor_get(v___x_2011_, 0);
                            v_snd_2013_ = crate::leanh::lean_ctor_get(v___x_2011_, 1);
                            v_isSharedCheck_2039_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2011_)) as u8;
                            if v_isSharedCheck_2039_ == 0 {
                                v___x_2015_ = v___x_2011_;
                                v_isShared_2016_ = v_isSharedCheck_2039_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_2013_);
                                crate::leanh::lean_inc(v_fst_2012_);
                                crate::leanh::lean_dec(v___x_2011_);
                                v___x_2015_ = crate::leanh::lean_box(0);
                                v_isShared_2016_ = v_isSharedCheck_2039_;
                                state = 26;
                                continue;
                            }
                        }
                        10 => {
                            v_data_2040_ = crate::leanh::lean_ctor_get(v_e_1805_, 0);
                            v_expr_2041_ = crate::leanh::lean_ctor_get(v_e_1805_, 1);
                            crate::leanh::lean_inc_ref(v_expr_2041_);
                            v___x_2042_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_expr_2041_,
                                v_a_1806_,
                            );
                            v_fst_2043_ = crate::leanh::lean_ctor_get(v___x_2042_, 0);
                            v_snd_2044_ = crate::leanh::lean_ctor_get(v___x_2042_, 1);
                            v_isSharedCheck_2058_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2042_)) as u8;
                            if v_isSharedCheck_2058_ == 0 {
                                v___x_2046_ = v___x_2042_;
                                v_isShared_2047_ = v_isSharedCheck_2058_;
                                state = 31;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_2044_);
                                crate::leanh::lean_inc(v_fst_2043_);
                                crate::leanh::lean_dec(v___x_2042_);
                                v___x_2046_ = crate::leanh::lean_box(0);
                                v_isShared_2047_ = v_isSharedCheck_2058_;
                                state = 31;
                                continue;
                            }
                        }
                        11 => {
                            v_typeName_2059_ = crate::leanh::lean_ctor_get(v_e_1805_, 0);
                            v_idx_2060_ = crate::leanh::lean_ctor_get(v_e_1805_, 1);
                            v_struct_2061_ = crate::leanh::lean_ctor_get(v_e_1805_, 2);
                            crate::leanh::lean_inc_ref(v_struct_2061_);
                            v___x_2062_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_struct_2061_,
                                v_a_1806_,
                            );
                            v_fst_2063_ = crate::leanh::lean_ctor_get(v___x_2062_, 0);
                            v_snd_2064_ = crate::leanh::lean_ctor_get(v___x_2062_, 1);
                            v_isSharedCheck_2078_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2062_)) as u8;
                            if v_isSharedCheck_2078_ == 0 {
                                v___x_2066_ = v___x_2062_;
                                v_isShared_2067_ = v_isSharedCheck_2078_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_2064_);
                                crate::leanh::lean_inc(v_fst_2063_);
                                crate::leanh::lean_dec(v___x_2062_);
                                v___x_2066_ = crate::leanh::lean_box(0);
                                v_isShared_2067_ = v_isSharedCheck_2078_;
                                state = 34;
                                continue;
                            }
                        }
                        _ => {
                            v___x_2079_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2079_, 0, v_e_1805_);
                            crate::leanh::lean_ctor_set(v___x_2079_, 1, v_a_1806_);
                            return v___x_2079_;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_fst_1827_);
                v___x_1832_ = l_Lean_mkFVar(v_fst_1827_);
                v___x_1861_ = l_Lean_Name_isAnonymous(v_userName_1813_);
                if v___x_1861_ == 0 {
                    v_userName_1834_ = v_userName_1813_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_userName_1813_);
                    v_fvars_1862_ = crate::leanh::lean_ctor_get(v_snd_1828_, 5);
                    v___x_1863_ = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1;
                    v___x_1864_ = lean_array_get_size(v_fvars_1862_);
                    v___x_1865_ = lean_name_append_index_after(v___x_1863_, v___x_1864_);
                    v_userName_1834_ = v___x_1865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_ngen_1835_ = crate::leanh::lean_ctor_get(v_snd_1828_, 0);
                v_lctx_1836_ = crate::leanh::lean_ctor_get(v_snd_1828_, 1);
                v_mctx_1837_ = crate::leanh::lean_ctor_get(v_snd_1828_, 2);
                v_nextParamIdx_1838_ = crate::leanh::lean_ctor_get(v_snd_1828_, 3);
                v_paramNames_1839_ = crate::leanh::lean_ctor_get(v_snd_1828_, 4);
                v_fvars_1840_ = crate::leanh::lean_ctor_get(v_snd_1828_, 5);
                v_mvars_1841_ = crate::leanh::lean_ctor_get(v_snd_1828_, 6);
                v_lmap_1842_ = crate::leanh::lean_ctor_get(v_snd_1828_, 7);
                v_emap_1843_ = crate::leanh::lean_ctor_get(v_snd_1828_, 8);
                v_abstractLevels_1844_ = crate::leanh::lean_ctor_get_uint8(
                    v_snd_1828_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_isSharedCheck_1860_ = (!crate::leanh::lean_is_exclusive(v_snd_1828_)) as u8;
                if v_isSharedCheck_1860_ == 0 {
                    v___x_1846_ = v_snd_1828_;
                    v_isShared_1847_ = v_isSharedCheck_1860_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_emap_1843_);
                    crate::leanh::lean_inc(v_lmap_1842_);
                    crate::leanh::lean_inc(v_mvars_1841_);
                    crate::leanh::lean_inc(v_fvars_1840_);
                    crate::leanh::lean_inc(v_paramNames_1839_);
                    crate::leanh::lean_inc(v_nextParamIdx_1838_);
                    crate::leanh::lean_inc(v_mctx_1837_);
                    crate::leanh::lean_inc(v_lctx_1836_);
                    crate::leanh::lean_inc(v_ngen_1835_);
                    crate::leanh::lean_dec(v_snd_1828_);
                    v___x_1846_ = crate::leanh::lean_box(0);
                    v_isShared_1847_ = v_isSharedCheck_1860_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1848_ = 0;
                v___x_1849_ = 0;
                v___x_1850_ = l_Lean_LocalContext_mkLocalDecl(
                    v_lctx_1836_,
                    v_fst_1827_,
                    v_userName_1834_,
                    v_fst_1824_,
                    v___x_1848_,
                    v___x_1849_,
                );
                crate::leanh::lean_inc_ref_n(v___x_1832_, 2);
                v___x_1851_ = lean_array_push(v_fvars_1840_, v___x_1832_);
                v___x_1852_ = lean_array_push(v_mvars_1841_, v_e_1805_);
                v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_emap_1843_, v_mvarId_1809_, v___x_1832_);
                if v_isShared_1847_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1846_, 8, v___x_1853_);
                    crate::leanh::lean_ctor_set(v___x_1846_, 6, v___x_1852_);
                    crate::leanh::lean_ctor_set(v___x_1846_, 5, v___x_1851_);
                    crate::leanh::lean_ctor_set(v___x_1846_, 1, v___x_1850_);
                    v___x_1855_ = v___x_1846_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1859_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_ngen_1835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___x_1850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_mctx_1837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_nextParamIdx_1838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_paramNames_1839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 5, v___x_1851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 6, v___x_1852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 7, v_lmap_1842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 8, v___x_1853_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1859_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1844_,
                    );
                    v___x_1855_ = v_reuseFailAlloc_1859_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1830_, 1, v___x_1855_);
                    crate::leanh::lean_ctor_set(v___x_1830_, 0, v___x_1832_);
                    v___x_1857_ = v___x_1830_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1855_);
                    v___x_1857_ = v_reuseFailAlloc_1858_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1857_;
            }
            6 => {
                v___x_1876_ = lean_ptr_addr(v_u_1869_);
                v___x_1877_ = lean_ptr_addr(v_fst_1871_);
                v___x_1878_ = lean_usize_dec_eq(v___x_1876_, v___x_1877_);
                if v___x_1878_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_1805_, 1);
                    v___x_1879_ = l_Lean_Expr_sort___override(v_fst_1871_);
                    if v_isShared_1875_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1874_, 0, v___x_1879_);
                        v___x_1881_ = v___x_1874_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1882_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_snd_1872_);
                        v___x_1881_ = v_reuseFailAlloc_1882_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1871_);
                    if v_isShared_1875_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1874_, 0, v_e_1805_);
                        v___x_1884_ = v___x_1874_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1885_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_e_1805_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_snd_1872_);
                        v___x_1884_ = v_reuseFailAlloc_1885_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_1881_;
            }
            8 => {
                return v___x_1884_;
            }
            9 => {
                v___x_1896_ = l_ptrEqList___redArg(v_us_1888_, v_fst_1891_);
                if v___x_1896_ == 0 {
                    crate::leanh::lean_inc(v_declName_1887_);
                    crate::leanh::lean_dec_ref_known(v_e_1805_, 2);
                    v___x_1897_ = l_Lean_Expr_const___override(v_declName_1887_, v_fst_1891_);
                    if v_isShared_1895_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1894_, 0, v___x_1897_);
                        v___x_1899_ = v___x_1894_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1900_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_snd_1892_);
                        v___x_1899_ = v_reuseFailAlloc_1900_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1891_);
                    if v_isShared_1895_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1894_, 0, v_e_1805_);
                        v___x_1902_ = v___x_1894_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1903_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_e_1805_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_snd_1892_);
                        v___x_1902_ = v_reuseFailAlloc_1903_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_1899_;
            }
            11 => {
                return v___x_1902_;
            }
            12 => {
                v___x_1925_ = lean_ptr_addr(v_fn_1905_);
                v___x_1926_ = lean_ptr_addr(v_fst_1908_);
                v___x_1927_ = lean_usize_dec_eq(v___x_1925_, v___x_1926_);
                if v___x_1927_ == 0 {
                    v___y_1917_ = v___x_1927_;
                    state = 13;
                    continue;
                } else {
                    v___x_1928_ = lean_ptr_addr(v_arg_1906_);
                    v___x_1929_ = lean_ptr_addr(v_fst_1911_);
                    v___x_1930_ = lean_usize_dec_eq(v___x_1928_, v___x_1929_);
                    v___y_1917_ = v___x_1930_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_1917_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_1805_, 2);
                    v___x_1918_ = l_Lean_Expr_app___override(v_fst_1908_, v_fst_1911_);
                    if v_isShared_1915_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1918_);
                        v___x_1920_ = v___x_1914_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1921_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_snd_1912_);
                        v___x_1920_ = v_reuseFailAlloc_1921_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1911_);
                    crate::leanh::lean_dec(v_fst_1908_);
                    if v_isShared_1915_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1914_, 0, v_e_1805_);
                        v___x_1923_ = v___x_1914_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1924_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_e_1805_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_snd_1912_);
                        v___x_1923_ = v_reuseFailAlloc_1924_;
                        state = 15;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_1920_;
            }
            15 => {
                return v___x_1923_;
            }
            16 => {
                v___x_1959_ = lean_ptr_addr(v_binderType_1933_);
                v___x_1960_ = lean_ptr_addr(v_fst_1937_);
                v___x_1961_ = lean_usize_dec_eq(v___x_1959_, v___x_1960_);
                if v___x_1961_ == 0 {
                    v___y_1946_ = v___x_1961_;
                    state = 17;
                    continue;
                } else {
                    v___x_1962_ = lean_ptr_addr(v_body_1934_);
                    v___x_1963_ = lean_ptr_addr(v_fst_1940_);
                    v___x_1964_ = lean_usize_dec_eq(v___x_1962_, v___x_1963_);
                    v___y_1946_ = v___x_1964_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v___y_1946_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1932_);
                    crate::leanh::lean_dec_ref_known(v_e_1805_, 3);
                    v___x_1947_ = l_Lean_Expr_lam___override(
                        v_binderName_1932_,
                        v_fst_1937_,
                        v_fst_1940_,
                        v_binderInfo_1935_,
                    );
                    if v_isShared_1944_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1947_);
                        v___x_1949_ = v___x_1943_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_snd_1941_);
                        v___x_1949_ = v_reuseFailAlloc_1950_;
                        state = 18;
                        continue;
                    }
                } else {
                    v___x_1951_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1935_, v_binderInfo_1935_);
                    if v___x_1951_ == 0 {
                        crate::leanh::lean_inc(v_binderName_1932_);
                        crate::leanh::lean_dec_ref_known(v_e_1805_, 3);
                        v___x_1952_ = l_Lean_Expr_lam___override(
                            v_binderName_1932_,
                            v_fst_1937_,
                            v_fst_1940_,
                            v_binderInfo_1935_,
                        );
                        if v_isShared_1944_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1952_);
                            v___x_1954_ = v___x_1943_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1955_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_snd_1941_);
                            v___x_1954_ = v_reuseFailAlloc_1955_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_1940_);
                        crate::leanh::lean_dec(v_fst_1937_);
                        if v_isShared_1944_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1943_, 0, v_e_1805_);
                            v___x_1957_ = v___x_1943_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_1958_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_e_1805_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_snd_1941_);
                            v___x_1957_ = v_reuseFailAlloc_1958_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            18 => {
                return v___x_1949_;
            }
            19 => {
                return v___x_1954_;
            }
            20 => {
                return v___x_1957_;
            }
            21 => {
                v___x_1993_ = lean_ptr_addr(v_binderType_1967_);
                v___x_1994_ = lean_ptr_addr(v_fst_1971_);
                v___x_1995_ = lean_usize_dec_eq(v___x_1993_, v___x_1994_);
                if v___x_1995_ == 0 {
                    v___y_1980_ = v___x_1995_;
                    state = 22;
                    continue;
                } else {
                    v___x_1996_ = lean_ptr_addr(v_body_1968_);
                    v___x_1997_ = lean_ptr_addr(v_fst_1974_);
                    v___x_1998_ = lean_usize_dec_eq(v___x_1996_, v___x_1997_);
                    v___y_1980_ = v___x_1998_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v___y_1980_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1966_);
                    crate::leanh::lean_dec_ref_known(v_e_1805_, 3);
                    v___x_1981_ = l_Lean_Expr_forallE___override(
                        v_binderName_1966_,
                        v_fst_1971_,
                        v_fst_1974_,
                        v_binderInfo_1969_,
                    );
                    if v_isShared_1978_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1977_, 0, v___x_1981_);
                        v___x_1983_ = v___x_1977_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_snd_1975_);
                        v___x_1983_ = v_reuseFailAlloc_1984_;
                        state = 23;
                        continue;
                    }
                } else {
                    v___x_1985_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1969_, v_binderInfo_1969_);
                    if v___x_1985_ == 0 {
                        crate::leanh::lean_inc(v_binderName_1966_);
                        crate::leanh::lean_dec_ref_known(v_e_1805_, 3);
                        v___x_1986_ = l_Lean_Expr_forallE___override(
                            v_binderName_1966_,
                            v_fst_1971_,
                            v_fst_1974_,
                            v_binderInfo_1969_,
                        );
                        if v_isShared_1978_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1977_, 0, v___x_1986_);
                            v___x_1988_ = v___x_1977_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_1989_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_snd_1975_);
                            v___x_1988_ = v_reuseFailAlloc_1989_;
                            state = 24;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_1974_);
                        crate::leanh::lean_dec(v_fst_1971_);
                        if v_isShared_1978_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1977_, 0, v_e_1805_);
                            v___x_1991_ = v___x_1977_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_1992_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_e_1805_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_snd_1975_);
                            v___x_1991_ = v_reuseFailAlloc_1992_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            23 => {
                return v___x_1983_;
            }
            24 => {
                return v___x_1988_;
            }
            25 => {
                return v___x_1991_;
            }
            26 => {
                v___x_2033_ = lean_ptr_addr(v_type_2001_);
                v___x_2034_ = lean_ptr_addr(v_fst_2006_);
                v___x_2035_ = lean_usize_dec_eq(v___x_2033_, v___x_2034_);
                if v___x_2035_ == 0 {
                    v___y_2018_ = v___x_2035_;
                    state = 27;
                    continue;
                } else {
                    v___x_2036_ = lean_ptr_addr(v_value_2002_);
                    v___x_2037_ = lean_ptr_addr(v_fst_2009_);
                    v___x_2038_ = lean_usize_dec_eq(v___x_2036_, v___x_2037_);
                    v___y_2018_ = v___x_2038_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v___y_2018_ == 0 {
                    crate::leanh::lean_inc(v_declName_2000_);
                    crate::leanh::lean_dec_ref_known(v_e_1805_, 4);
                    v___x_2019_ = l_Lean_Expr_letE___override(
                        v_declName_2000_,
                        v_fst_2006_,
                        v_fst_2009_,
                        v_fst_2012_,
                        v_nondep_2004_,
                    );
                    if v_isShared_2016_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2015_, 0, v___x_2019_);
                        v___x_2021_ = v___x_2015_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_2022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_snd_2013_);
                        v___x_2021_ = v_reuseFailAlloc_2022_;
                        state = 28;
                        continue;
                    }
                } else {
                    v___x_2023_ = lean_ptr_addr(v_body_2003_);
                    v___x_2024_ = lean_ptr_addr(v_fst_2012_);
                    v___x_2025_ = lean_usize_dec_eq(v___x_2023_, v___x_2024_);
                    if v___x_2025_ == 0 {
                        crate::leanh::lean_inc(v_declName_2000_);
                        crate::leanh::lean_dec_ref_known(v_e_1805_, 4);
                        v___x_2026_ = l_Lean_Expr_letE___override(
                            v_declName_2000_,
                            v_fst_2006_,
                            v_fst_2009_,
                            v_fst_2012_,
                            v_nondep_2004_,
                        );
                        if v_isShared_2016_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2015_, 0, v___x_2026_);
                            v___x_2028_ = v___x_2015_;
                            state = 29;
                            continue;
                        } else {
                            v_reuseFailAlloc_2029_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_snd_2013_);
                            v___x_2028_ = v_reuseFailAlloc_2029_;
                            state = 29;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_2012_);
                        crate::leanh::lean_dec(v_fst_2009_);
                        crate::leanh::lean_dec(v_fst_2006_);
                        if v_isShared_2016_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2015_, 0, v_e_1805_);
                            v___x_2031_ = v___x_2015_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_2032_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_e_1805_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_snd_2013_);
                            v___x_2031_ = v_reuseFailAlloc_2032_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            28 => {
                return v___x_2021_;
            }
            29 => {
                return v___x_2028_;
            }
            30 => {
                return v___x_2031_;
            }
            31 => {
                v___x_2048_ = lean_ptr_addr(v_expr_2041_);
                v___x_2049_ = lean_ptr_addr(v_fst_2043_);
                v___x_2050_ = lean_usize_dec_eq(v___x_2048_, v___x_2049_);
                if v___x_2050_ == 0 {
                    crate::leanh::lean_inc(v_data_2040_);
                    crate::leanh::lean_dec_ref_known(v_e_1805_, 2);
                    v___x_2051_ = l_Lean_Expr_mdata___override(v_data_2040_, v_fst_2043_);
                    if v_isShared_2047_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2046_, 0, v___x_2051_);
                        v___x_2053_ = v___x_2046_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_2054_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_snd_2044_);
                        v___x_2053_ = v_reuseFailAlloc_2054_;
                        state = 32;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_2043_);
                    if v_isShared_2047_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2046_, 0, v_e_1805_);
                        v___x_2056_ = v___x_2046_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_e_1805_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2044_);
                        v___x_2056_ = v_reuseFailAlloc_2057_;
                        state = 33;
                        continue;
                    }
                }
            }
            32 => {
                return v___x_2053_;
            }
            33 => {
                return v___x_2056_;
            }
            34 => {
                v___x_2068_ = lean_ptr_addr(v_struct_2061_);
                v___x_2069_ = lean_ptr_addr(v_fst_2063_);
                v___x_2070_ = lean_usize_dec_eq(v___x_2068_, v___x_2069_);
                if v___x_2070_ == 0 {
                    crate::leanh::lean_inc(v_idx_2060_);
                    crate::leanh::lean_inc(v_typeName_2059_);
                    crate::leanh::lean_dec_ref_known(v_e_1805_, 3);
                    v___x_2071_ =
                        l_Lean_Expr_proj___override(v_typeName_2059_, v_idx_2060_, v_fst_2063_);
                    if v_isShared_2067_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2066_, 0, v___x_2071_);
                        v___x_2073_ = v___x_2066_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_2074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_snd_2064_);
                        v___x_2073_ = v_reuseFailAlloc_2074_;
                        state = 35;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_2063_);
                    if v_isShared_2067_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2066_, 0, v_e_1805_);
                        v___x_2076_ = v___x_2066_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_e_1805_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_snd_2064_);
                        v___x_2076_ = v_reuseFailAlloc_2077_;
                        state = 36;
                        continue;
                    }
                }
            }
            35 => {
                return v___x_2073_;
            }
            36 => {
                return v___x_2076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(
    mut v_00_u03b2_2080_: *mut crate::leanh::LeanObject,
    mut v_m_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_2081_, v_a_2082_);
    return v___x_2083_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(
    mut v_00_u03b2_2084_: *mut crate::leanh::LeanObject,
    mut v_m_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(v_00_u03b2_2084_, v_m_2085_, v_a_2086_);
    crate::leanh::lean_dec(v_a_2086_);
    crate::leanh::lean_dec_ref(v_m_2085_);
    return v_res_2087_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(
    mut v_00_u03b2_2088_: *mut crate::leanh::LeanObject,
    mut v_m_2089_: *mut crate::leanh::LeanObject,
    mut v_a_2090_: *mut crate::leanh::LeanObject,
    mut v_b_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_2089_, v_a_2090_, v_b_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(
    mut v_00_u03b2_2093_: *mut crate::leanh::LeanObject,
    mut v_a_2094_: *mut crate::leanh::LeanObject,
    mut v_x_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_2094_, v_x_2095_);
    return v___x_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_x_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(v_00_u03b2_2097_, v_a_2098_, v_x_2099_);
    crate::leanh::lean_dec(v_x_2099_);
    crate::leanh::lean_dec(v_a_2098_);
    return v_res_2100_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(
    mut v_00_u03b2_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
    mut v_x_2103_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2104_: u8 = 0;
    v___x_2104_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_2102_, v_x_2103_);
    return v___x_2104_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(
    mut v_00_u03b2_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2108_: u8 = 0;
    let mut v_r_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(v_00_u03b2_2105_, v_a_2106_, v_x_2107_);
    crate::leanh::lean_dec(v_x_2107_);
    crate::leanh::lean_dec(v_a_2106_);
    v_r_2109_ = crate::leanh::lean_box((v_res_2108_) as usize);
    return v_r_2109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4(
    mut v_00_u03b2_2110_: *mut crate::leanh::LeanObject,
    mut v_data_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_data_2111_);
    return v___x_2112_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5(
    mut v_00_u03b2_2113_: *mut crate::leanh::LeanObject,
    mut v_a_2114_: *mut crate::leanh::LeanObject,
    mut v_b_2115_: *mut crate::leanh::LeanObject,
    mut v_x_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_2114_, v_b_2115_, v_x_2116_);
    return v___x_2117_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2118_: *mut crate::leanh::LeanObject,
    mut v_i_2119_: *mut crate::leanh::LeanObject,
    mut v_source_2120_: *mut crate::leanh::LeanObject,
    mut v_target_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v_i_2119_, v_source_2120_, v_target_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7(
    mut v_00_u03b2_2123_: *mut crate::leanh::LeanObject,
    mut v_x_2124_: *mut crate::leanh::LeanObject,
    mut v_x_2125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_x_2124_, v_x_2125_);
    return v___x_2126_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
    mut v_e_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: u8 = 0;
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_unused_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2130_ = l_Lean_Expr_hasMVar(v_e_2127_);
                if v___x_2130_ == 0 {
                    v___x_2131_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2131_, 0, v_e_2127_);
                    return v___x_2131_;
                } else {
                    v___x_2132_ = lean_st_ref_get(v___y_2128_);
                    v_mctx_2133_ = crate::leanh::lean_ctor_get(v___x_2132_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2133_);
                    crate::leanh::lean_dec(v___x_2132_);
                    v___x_2134_ = l_Lean_instantiateMVarsCore(v_mctx_2133_, v_e_2127_);
                    v_fst_2135_ = crate::leanh::lean_ctor_get(v___x_2134_, 0);
                    crate::leanh::lean_inc(v_fst_2135_);
                    v_snd_2136_ = crate::leanh::lean_ctor_get(v___x_2134_, 1);
                    crate::leanh::lean_inc(v_snd_2136_);
                    crate::leanh::lean_dec_ref(v___x_2134_);
                    v___x_2137_ = lean_st_ref_take(v___y_2128_);
                    v_cache_2138_ = crate::leanh::lean_ctor_get(v___x_2137_, 1);
                    v_zetaDeltaFVarIds_2139_ = crate::leanh::lean_ctor_get(v___x_2137_, 2);
                    v_postponed_2140_ = crate::leanh::lean_ctor_get(v___x_2137_, 3);
                    v_diag_2141_ = crate::leanh::lean_ctor_get(v___x_2137_, 4);
                    v_isSharedCheck_2150_ = (!crate::leanh::lean_is_exclusive(v___x_2137_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v_unused_2151_ = crate::leanh::lean_ctor_get(v___x_2137_, 0);
                        crate::leanh::lean_dec(v_unused_2151_);
                        v___x_2143_ = v___x_2137_;
                        v_isShared_2144_ = v_isSharedCheck_2150_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2141_);
                        crate::leanh::lean_inc(v_postponed_2140_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2139_);
                        crate::leanh::lean_inc(v_cache_2138_);
                        crate::leanh::lean_dec(v___x_2137_);
                        v___x_2143_ = crate::leanh::lean_box(0);
                        v_isShared_2144_ = v_isSharedCheck_2150_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2143_, 0, v_snd_2136_);
                    v___x_2146_ = v___x_2143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_snd_2136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_cache_2138_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2149_,
                        2,
                        v_zetaDeltaFVarIds_2139_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_postponed_2140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_diag_2141_);
                    v___x_2146_ = v_reuseFailAlloc_2149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2147_ = lean_st_ref_set(v___y_2128_, v___x_2146_);
                v___x_2148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2148_, 0, v_fst_2135_);
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(
    mut v_e_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2155_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
        v_e_2152_,
        v___y_2153_,
    );
    crate::leanh::lean_dec(v___y_2153_);
    return v_res_2155_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(
    mut v_e_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
    mut v___y_2159_: *mut crate::leanh::LeanObject,
    mut v___y_2160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2162_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
        v_e_2156_,
        v___y_2158_,
    );
    return v___x_2162_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(
    mut v_e_2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
    mut v___y_2165_: *mut crate::leanh::LeanObject,
    mut v___y_2166_: *mut crate::leanh::LeanObject,
    mut v___y_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(
        v_e_2163_,
        v___y_2164_,
        v___y_2165_,
        v___y_2166_,
        v___y_2167_,
    );
    crate::leanh::lean_dec(v___y_2167_);
    crate::leanh::lean_dec_ref(v___y_2166_);
    crate::leanh::lean_dec(v___y_2165_);
    crate::leanh::lean_dec_ref(v___y_2164_);
    return v_res_2169_;
}
pub unsafe fn _init_l_Lean_Meta_abstractMVars___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = crate::leanh::lean_box(0);
    v___x_2173_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2174_ = lean_mk_array(v___x_2173_, v___x_2172_);
    return v___x_2174_;
}
pub unsafe fn _init_l_Lean_Meta_abstractMVars___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2175_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__1_once),
        _init_l_Lean_Meta_abstractMVars___closed__1,
    );
    v___x_2176_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2177_, 0, v___x_2176_);
    crate::leanh::lean_ctor_set(v___x_2177_, 1, v___x_2175_);
    return v___x_2177_;
}
pub unsafe fn l_Lean_Meta_abstractMVars(
    mut v_e_2178_: *mut crate::leanh::LeanObject,
    mut v_levels_2179_: u8,
    mut v_a_2180_: *mut crate::leanh::LeanObject,
    mut v_a_2181_: *mut crate::leanh::LeanObject,
    mut v_a_2182_: *mut crate::leanh::LeanObject,
    mut v_a_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_unused_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_unused_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2185_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
                        v_e_2178_, v_a_2181_,
                    );
                v_a_2186_ = crate::leanh::lean_ctor_get(v___x_2185_, 0);
                v_isSharedCheck_2247_ = (!crate::leanh::lean_is_exclusive(v___x_2185_)) as u8;
                if v_isSharedCheck_2247_ == 0 {
                    v___x_2188_ = v___x_2185_;
                    v_isShared_2189_ = v_isSharedCheck_2247_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2186_);
                    crate::leanh::lean_dec(v___x_2185_);
                    v___x_2188_ = crate::leanh::lean_box(0);
                    v_isShared_2189_ = v_isSharedCheck_2247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2190_ = lean_st_ref_get(v_a_2181_);
                v___x_2191_ = lean_st_ref_get(v_a_2183_);
                v_mctx_2192_ = crate::leanh::lean_ctor_get(v___x_2190_, 0);
                crate::leanh::lean_inc_ref(v_mctx_2192_);
                crate::leanh::lean_dec(v___x_2190_);
                v_lctx_2193_ = crate::leanh::lean_ctor_get(v_a_2180_, 2);
                v_ngen_2194_ = crate::leanh::lean_ctor_get(v___x_2191_, 2);
                crate::leanh::lean_inc_ref(v_ngen_2194_);
                crate::leanh::lean_dec(v___x_2191_);
                v___x_2195_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2196_ = l_Lean_Meta_abstractMVars___closed__0;
                v___x_2197_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__2_once),
                    _init_l_Lean_Meta_abstractMVars___closed__2,
                );
                crate::leanh::lean_inc_ref(v_lctx_2193_);
                v___x_2198_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2198_, 0, v_ngen_2194_);
                crate::leanh::lean_ctor_set(v___x_2198_, 1, v_lctx_2193_);
                crate::leanh::lean_ctor_set(v___x_2198_, 2, v_mctx_2192_);
                crate::leanh::lean_ctor_set(v___x_2198_, 3, v___x_2195_);
                crate::leanh::lean_ctor_set(v___x_2198_, 4, v___x_2196_);
                crate::leanh::lean_ctor_set(v___x_2198_, 5, v___x_2196_);
                crate::leanh::lean_ctor_set(v___x_2198_, 6, v___x_2196_);
                crate::leanh::lean_ctor_set(v___x_2198_, 7, v___x_2197_);
                crate::leanh::lean_ctor_set(v___x_2198_, 8, v___x_2197_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2198_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                    v_levels_2179_,
                );
                v___x_2199_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_a_2186_, v___x_2198_);
                v_fst_2200_ = crate::leanh::lean_ctor_get(v___x_2199_, 0);
                crate::leanh::lean_inc(v_fst_2200_);
                v_snd_2201_ = crate::leanh::lean_ctor_get(v___x_2199_, 1);
                crate::leanh::lean_inc(v_snd_2201_);
                crate::leanh::lean_dec_ref(v___x_2199_);
                v___x_2202_ = lean_st_ref_take(v_a_2183_);
                v_ngen_2203_ = crate::leanh::lean_ctor_get(v_snd_2201_, 0);
                crate::leanh::lean_inc_ref(v_ngen_2203_);
                v_lctx_2204_ = crate::leanh::lean_ctor_get(v_snd_2201_, 1);
                crate::leanh::lean_inc_ref(v_lctx_2204_);
                v_mctx_2205_ = crate::leanh::lean_ctor_get(v_snd_2201_, 2);
                crate::leanh::lean_inc_ref(v_mctx_2205_);
                v_paramNames_2206_ = crate::leanh::lean_ctor_get(v_snd_2201_, 4);
                crate::leanh::lean_inc_ref(v_paramNames_2206_);
                v_fvars_2207_ = crate::leanh::lean_ctor_get(v_snd_2201_, 5);
                crate::leanh::lean_inc_ref(v_fvars_2207_);
                v_mvars_2208_ = crate::leanh::lean_ctor_get(v_snd_2201_, 6);
                crate::leanh::lean_inc_ref(v_mvars_2208_);
                crate::leanh::lean_dec(v_snd_2201_);
                v_env_2209_ = crate::leanh::lean_ctor_get(v___x_2202_, 0);
                v_nextMacroScope_2210_ = crate::leanh::lean_ctor_get(v___x_2202_, 1);
                v_auxDeclNGen_2211_ = crate::leanh::lean_ctor_get(v___x_2202_, 3);
                v_traceState_2212_ = crate::leanh::lean_ctor_get(v___x_2202_, 4);
                v_cache_2213_ = crate::leanh::lean_ctor_get(v___x_2202_, 5);
                v_messages_2214_ = crate::leanh::lean_ctor_get(v___x_2202_, 6);
                v_infoState_2215_ = crate::leanh::lean_ctor_get(v___x_2202_, 7);
                v_snapshotTasks_2216_ = crate::leanh::lean_ctor_get(v___x_2202_, 8);
                v_isSharedCheck_2245_ = (!crate::leanh::lean_is_exclusive(v___x_2202_)) as u8;
                if v_isSharedCheck_2245_ == 0 {
                    v_unused_2246_ = crate::leanh::lean_ctor_get(v___x_2202_, 2);
                    crate::leanh::lean_dec(v_unused_2246_);
                    v___x_2218_ = v___x_2202_;
                    v_isShared_2219_ = v_isSharedCheck_2245_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2216_);
                    crate::leanh::lean_inc(v_infoState_2215_);
                    crate::leanh::lean_inc(v_messages_2214_);
                    crate::leanh::lean_inc(v_cache_2213_);
                    crate::leanh::lean_inc(v_traceState_2212_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2211_);
                    crate::leanh::lean_inc(v_nextMacroScope_2210_);
                    crate::leanh::lean_inc(v_env_2209_);
                    crate::leanh::lean_dec(v___x_2202_);
                    v___x_2218_ = crate::leanh::lean_box(0);
                    v_isShared_2219_ = v_isSharedCheck_2245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2218_, 2, v_ngen_2203_);
                    v___x_2221_ = v___x_2218_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2244_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_env_2209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_nextMacroScope_2210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_ngen_2203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_auxDeclNGen_2211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_traceState_2212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 5, v_cache_2213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 6, v_messages_2214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 7, v_infoState_2215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 8, v_snapshotTasks_2216_);
                    v___x_2221_ = v_reuseFailAlloc_2244_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2222_ = lean_st_ref_set(v_a_2183_, v___x_2221_);
                v___x_2223_ = lean_st_ref_take(v_a_2181_);
                v_cache_2224_ = crate::leanh::lean_ctor_get(v___x_2223_, 1);
                v_zetaDeltaFVarIds_2225_ = crate::leanh::lean_ctor_get(v___x_2223_, 2);
                v_postponed_2226_ = crate::leanh::lean_ctor_get(v___x_2223_, 3);
                v_diag_2227_ = crate::leanh::lean_ctor_get(v___x_2223_, 4);
                v_isSharedCheck_2242_ = (!crate::leanh::lean_is_exclusive(v___x_2223_)) as u8;
                if v_isSharedCheck_2242_ == 0 {
                    v_unused_2243_ = crate::leanh::lean_ctor_get(v___x_2223_, 0);
                    crate::leanh::lean_dec(v_unused_2243_);
                    v___x_2229_ = v___x_2223_;
                    v_isShared_2230_ = v_isSharedCheck_2242_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2227_);
                    crate::leanh::lean_inc(v_postponed_2226_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2225_);
                    crate::leanh::lean_inc(v_cache_2224_);
                    crate::leanh::lean_dec(v___x_2223_);
                    v___x_2229_ = crate::leanh::lean_box(0);
                    v_isShared_2230_ = v_isSharedCheck_2242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2230_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2229_, 0, v_mctx_2205_);
                    v___x_2232_ = v___x_2229_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_mctx_2205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_cache_2224_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2241_,
                        2,
                        v_zetaDeltaFVarIds_2225_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_postponed_2226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_diag_2227_);
                    v___x_2232_ = v_reuseFailAlloc_2241_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2233_ = lean_st_ref_set(v_a_2181_, v___x_2232_);
                v___x_2234_ = 1;
                v___x_2235_ = 0;
                v___x_2236_ = l_Lean_LocalContext_mkLambda(
                    v_lctx_2204_,
                    v_fvars_2207_,
                    v_fst_2200_,
                    v___x_2234_,
                    v___x_2235_,
                );
                crate::leanh::lean_dec(v_fst_2200_);
                crate::leanh::lean_dec_ref(v_fvars_2207_);
                v___x_2237_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2237_, 0, v_paramNames_2206_);
                crate::leanh::lean_ctor_set(v___x_2237_, 1, v_mvars_2208_);
                crate::leanh::lean_ctor_set(v___x_2237_, 2, v___x_2236_);
                if v_isShared_2189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2188_, 0, v___x_2237_);
                    v___x_2239_ = v___x_2188_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
                    v___x_2239_ = v_reuseFailAlloc_2240_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_abstractMVars___boxed(
    mut v_e_2248_: *mut crate::leanh::LeanObject,
    mut v_levels_2249_: *mut crate::leanh::LeanObject,
    mut v_a_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
    mut v_a_2254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_levels_boxed_2255_: u8 = 0;
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_levels_boxed_2255_ = (crate::leanh::lean_unbox(v_levels_2249_) as u8);
    v_res_2256_ = l_Lean_Meta_abstractMVars(
        v_e_2248_,
        v_levels_boxed_2255_,
        v_a_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
    );
    crate::leanh::lean_dec(v_a_2253_);
    crate::leanh::lean_dec_ref(v_a_2252_);
    crate::leanh::lean_dec(v_a_2251_);
    crate::leanh::lean_dec_ref(v_a_2250_);
    return v_res_2256_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(
    mut v_sz_2257_: usize,
    mut v_i_2258_: usize,
    mut v_bs_2259_: *mut crate::leanh::LeanObject,
    mut v___y_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: usize = 0;
    let mut v___x_2272_: usize = 0;
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2265_ = lean_usize_dec_lt(v_i_2258_, v_sz_2257_);
                if v___x_2265_ == 0 {
                    v___x_2266_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2266_, 0, v_bs_2259_);
                    return v___x_2266_;
                } else {
                    v___x_2267_ = l_Lean_Meta_mkFreshLevelMVar(
                        v___y_2260_,
                        v___y_2261_,
                        v___y_2262_,
                        v___y_2263_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2267_) == 0 {
                        v_a_2268_ = crate::leanh::lean_ctor_get(v___x_2267_, 0);
                        crate::leanh::lean_inc(v_a_2268_);
                        crate::leanh::lean_dec_ref_known(v___x_2267_, 1);
                        v___x_2269_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2270_ = lean_array_uset(v_bs_2259_, v_i_2258_, v___x_2269_);
                        v___x_2271_ = 1usize;
                        v___x_2272_ = lean_usize_add(v_i_2258_, v___x_2271_);
                        v___x_2273_ = lean_array_uset(v_bs_x27_2270_, v_i_2258_, v_a_2268_);
                        v_i_2258_ = v___x_2272_;
                        v_bs_2259_ = v___x_2273_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_2259_);
                        v_a_2275_ = crate::leanh::lean_ctor_get(v___x_2267_, 0);
                        v_isSharedCheck_2282_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2267_)) as u8;
                        if v_isSharedCheck_2282_ == 0 {
                            v___x_2277_ = v___x_2267_;
                            v_isShared_2278_ = v_isSharedCheck_2282_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2275_);
                            crate::leanh::lean_dec(v___x_2267_);
                            v___x_2277_ = crate::leanh::lean_box(0);
                            v_isShared_2278_ = v_isSharedCheck_2282_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2278_ == 0 {
                    v___x_2280_ = v___x_2277_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
                    v___x_2280_ = v_reuseFailAlloc_2281_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0___boxed(
    mut v_sz_2283_: *mut crate::leanh::LeanObject,
    mut v_i_2284_: *mut crate::leanh::LeanObject,
    mut v_bs_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2291_: usize = 0;
    let mut v_i_boxed_2292_: usize = 0;
    let mut v_res_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2291_ = crate::leanh::lean_unbox_usize(v_sz_2283_);
    crate::leanh::lean_dec(v_sz_2283_);
    v_i_boxed_2292_ = crate::leanh::lean_unbox_usize(v_i_2284_);
    crate::leanh::lean_dec(v_i_2284_);
    v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_boxed_2291_, v_i_boxed_2292_, v_bs_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
    crate::leanh::lean_dec(v___y_2289_);
    crate::leanh::lean_dec_ref(v___y_2288_);
    crate::leanh::lean_dec(v___y_2287_);
    crate::leanh::lean_dec_ref(v___y_2286_);
    return v_res_2293_;
}
pub unsafe fn l_Lean_Meta_openAbstractMVarsResult(
    mut v_a_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
    mut v_a_2296_: *mut crate::leanh::LeanObject,
    mut v_a_2297_: *mut crate::leanh::LeanObject,
    mut v_a_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_paramNames_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2302_: usize = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_paramNames_2300_ = crate::leanh::lean_ctor_get(v_a_2294_, 0);
                v_expr_2301_ = crate::leanh::lean_ctor_get(v_a_2294_, 2);
                v_sz_2302_ = lean_array_size(v_paramNames_2300_);
                v___x_2303_ = 0usize;
                crate::leanh::lean_inc_ref(v_paramNames_2300_);
                v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_2302_, v___x_2303_, v_paramNames_2300_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
                if crate::leanh::lean_obj_tag(v___x_2304_) == 0 {
                    v_a_2305_ = crate::leanh::lean_ctor_get(v___x_2304_, 0);
                    crate::leanh::lean_inc(v_a_2305_);
                    crate::leanh::lean_dec_ref_known(v___x_2304_, 1);
                    crate::leanh::lean_inc_ref(v_paramNames_2300_);
                    v___x_2306_ = l_Lean_Expr_instantiateLevelParamsArray(
                        v_expr_2301_,
                        v_paramNames_2300_,
                        v_a_2305_,
                    );
                    v___x_2307_ = l_Lean_Meta_AbstractMVarsResult_numMVars(v_a_2294_);
                    crate::leanh::lean_dec_ref(v_a_2294_);
                    v___x_2308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
                    v___x_2309_ = l_Lean_Meta_lambdaMetaTelescope(
                        v___x_2306_,
                        v___x_2308_,
                        v_a_2295_,
                        v_a_2296_,
                        v_a_2297_,
                        v_a_2298_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_2308_, 1);
                    crate::leanh::lean_dec_ref(v___x_2306_);
                    return v___x_2309_;
                } else {
                    crate::leanh::lean_dec_ref(v_a_2294_);
                    v_a_2310_ = crate::leanh::lean_ctor_get(v___x_2304_, 0);
                    v_isSharedCheck_2317_ = (!crate::leanh::lean_is_exclusive(v___x_2304_)) as u8;
                    if v_isSharedCheck_2317_ == 0 {
                        v___x_2312_ = v___x_2304_;
                        v_isShared_2313_ = v_isSharedCheck_2317_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2310_);
                        crate::leanh::lean_dec(v___x_2304_);
                        v___x_2312_ = crate::leanh::lean_box(0);
                        v_isShared_2313_ = v_isSharedCheck_2317_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2313_ == 0 {
                    v___x_2315_ = v___x_2312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2316_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
                    v___x_2315_ = v_reuseFailAlloc_2316_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_openAbstractMVarsResult___boxed(
    mut v_a_2318_: *mut crate::leanh::LeanObject,
    mut v_a_2319_: *mut crate::leanh::LeanObject,
    mut v_a_2320_: *mut crate::leanh::LeanObject,
    mut v_a_2321_: *mut crate::leanh::LeanObject,
    mut v_a_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2324_ =
        l_Lean_Meta_openAbstractMVarsResult(v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
    crate::leanh::lean_dec(v_a_2322_);
    crate::leanh::lean_dec_ref(v_a_2321_);
    crate::leanh::lean_dec(v_a_2320_);
    crate::leanh::lean_dec_ref(v_a_2319_);
    return v_res_2324_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_AbstractMVars(
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
pub unsafe fn meta_initialize_Lean_Meta_AbstractMVars(
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
pub unsafe fn initialize_Lean_Meta_AbstractMVars(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Meta_AbstractMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_AbstractMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_AbstractMVars(builtin);
}
