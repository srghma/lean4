// Lean compiler output
// Module: Lean.Meta.AbstractMVars
// Imports: Lean.Meta.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_ptr_addr, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
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
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_get as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value:
    leanh::LeanClosureObject<7> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_bind as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 7,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_AbstractMVars_instMonadMCtxM: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [95, 97, 98, 115, 116, 77, 86, 97, 114, 0]};
static mut l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value) as *mut leanh::LeanObject,6357867680762384532 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value)
            as *mut leanh::LeanObject,
        13655884332201764339 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_abstractMVars___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_abstractMVars___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_abstractMVars___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_abstractMVars___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_abstractMVars___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_abstractMVars___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_abstractMVars___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(
    mut v_____do__lift_1163_: *mut leanh::LeanObject,
    mut v___y_1164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mctx_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mctx_1165_ = leanh::lean_ctor_get(v_____do__lift_1163_, 2);
    leanh::lean_inc_ref(v_mctx_1165_);
    v___x_1166_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1166_, 0, v_mctx_1165_);
    leanh::lean_ctor_set(v___x_1166_, 1, v___y_1164_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed(
    mut v_____do__lift_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ =
        l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(v_____do__lift_1167_, v___y_1168_);
    leanh::lean_dec_ref(v_____do__lift_1167_);
    return v_res_1169_;
}
pub unsafe fn l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1(
    mut v_f_1170_: *mut leanh::LeanObject,
    mut v___y_1171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ngen_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1181_: u8 = 0;
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ngen_1172_ = leanh::lean_ctor_get(v___y_1171_, 0);
                v_lctx_1173_ = leanh::lean_ctor_get(v___y_1171_, 1);
                v_mctx_1174_ = leanh::lean_ctor_get(v___y_1171_, 2);
                v_nextParamIdx_1175_ = leanh::lean_ctor_get(v___y_1171_, 3);
                v_paramNames_1176_ = leanh::lean_ctor_get(v___y_1171_, 4);
                v_fvars_1177_ = leanh::lean_ctor_get(v___y_1171_, 5);
                v_mvars_1178_ = leanh::lean_ctor_get(v___y_1171_, 6);
                v_lmap_1179_ = leanh::lean_ctor_get(v___y_1171_, 7);
                v_emap_1180_ = leanh::lean_ctor_get(v___y_1171_, 8);
                v_abstractLevels_1181_ = leanh::lean_ctor_get_uint8(
                    v___y_1171_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                );
                v_isSharedCheck_1191_ = (!leanh::lean_is_exclusive(v___y_1171_)) as u8;
                if v_isSharedCheck_1191_ == 0 {
                    v___x_1183_ = v___y_1171_;
                    v_isShared_1184_ = v_isSharedCheck_1191_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_emap_1180_);
                    leanh::lean_inc(v_lmap_1179_);
                    leanh::lean_inc(v_mvars_1178_);
                    leanh::lean_inc(v_fvars_1177_);
                    leanh::lean_inc(v_paramNames_1176_);
                    leanh::lean_inc(v_nextParamIdx_1175_);
                    leanh::lean_inc(v_mctx_1174_);
                    leanh::lean_inc(v_lctx_1173_);
                    leanh::lean_inc(v_ngen_1172_);
                    leanh::lean_dec(v___y_1171_);
                    v___x_1183_ = leanh::lean_box(0);
                    v_isShared_1184_ = v_isSharedCheck_1191_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1185_ = leanh::lean_box(0);
                v___x_1186_ = leanh::lean_apply_1(v_f_1170_, v_mctx_1174_);
                if v_isShared_1184_ == 0 {
                    leanh::lean_ctor_set(v___x_1183_, 2, v___x_1186_);
                    v___x_1188_ = v___x_1183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1190_ = leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_ngen_1172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_lctx_1173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 2, v___x_1186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_nextParamIdx_1175_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_paramNames_1176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 5, v_fvars_1177_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 6, v_mvars_1178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 7, v_lmap_1179_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 8, v_emap_1180_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1190_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1181_,
                    );
                    v___x_1188_ = v_reuseFailAlloc_1190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1189_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1189_, 0, v___x_1185_);
                leanh::lean_ctor_set(v___x_1189_, 1, v___x_1188_);
                return v___x_1189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractMVars_mkFreshId(
    mut v_a_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ngen_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1233_: u8 = 0;
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v_namePrefix_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1241_: u8 = 0;
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_isSharedCheck_1253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ngen_1224_ = leanh::lean_ctor_get(v_a_1223_, 0);
                v_lctx_1225_ = leanh::lean_ctor_get(v_a_1223_, 1);
                v_mctx_1226_ = leanh::lean_ctor_get(v_a_1223_, 2);
                v_nextParamIdx_1227_ = leanh::lean_ctor_get(v_a_1223_, 3);
                v_paramNames_1228_ = leanh::lean_ctor_get(v_a_1223_, 4);
                v_fvars_1229_ = leanh::lean_ctor_get(v_a_1223_, 5);
                v_mvars_1230_ = leanh::lean_ctor_get(v_a_1223_, 6);
                v_lmap_1231_ = leanh::lean_ctor_get(v_a_1223_, 7);
                v_emap_1232_ = leanh::lean_ctor_get(v_a_1223_, 8);
                v_abstractLevels_1233_ = leanh::lean_ctor_get_uint8(
                    v_a_1223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                );
                v_isSharedCheck_1253_ = (!leanh::lean_is_exclusive(v_a_1223_)) as u8;
                if v_isSharedCheck_1253_ == 0 {
                    v___x_1235_ = v_a_1223_;
                    v_isShared_1236_ = v_isSharedCheck_1253_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_emap_1232_);
                    leanh::lean_inc(v_lmap_1231_);
                    leanh::lean_inc(v_mvars_1230_);
                    leanh::lean_inc(v_fvars_1229_);
                    leanh::lean_inc(v_paramNames_1228_);
                    leanh::lean_inc(v_nextParamIdx_1227_);
                    leanh::lean_inc(v_mctx_1226_);
                    leanh::lean_inc(v_lctx_1225_);
                    leanh::lean_inc(v_ngen_1224_);
                    leanh::lean_dec(v_a_1223_);
                    v___x_1235_ = leanh::lean_box(0);
                    v_isShared_1236_ = v_isSharedCheck_1253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_namePrefix_1237_ = leanh::lean_ctor_get(v_ngen_1224_, 0);
                v_idx_1238_ = leanh::lean_ctor_get(v_ngen_1224_, 1);
                v_isSharedCheck_1252_ = (!leanh::lean_is_exclusive(v_ngen_1224_)) as u8;
                if v_isSharedCheck_1252_ == 0 {
                    v___x_1240_ = v_ngen_1224_;
                    v_isShared_1241_ = v_isSharedCheck_1252_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_1238_);
                    leanh::lean_inc(v_namePrefix_1237_);
                    leanh::lean_dec(v_ngen_1224_);
                    v___x_1240_ = leanh::lean_box(0);
                    v_isShared_1241_ = v_isSharedCheck_1252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_idx_1238_);
                leanh::lean_inc(v_namePrefix_1237_);
                v___x_1242_ = l_Lean_Name_num___override(v_namePrefix_1237_, v_idx_1238_);
                v___x_1243_ = leanh::lean_unsigned_to_nat(1);
                v___x_1244_ = lean_nat_add(v_idx_1238_, v___x_1243_);
                leanh::lean_dec(v_idx_1238_);
                if v_isShared_1241_ == 0 {
                    leanh::lean_ctor_set(v___x_1240_, 1, v___x_1244_);
                    v___x_1246_ = v___x_1240_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_namePrefix_1237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1244_);
                    v___x_1246_ = v_reuseFailAlloc_1251_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1236_ == 0 {
                    leanh::lean_ctor_set(v___x_1235_, 0, v___x_1246_);
                    v___x_1248_ = v___x_1235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1246_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_lctx_1225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_mctx_1226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_nextParamIdx_1227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_paramNames_1228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 5, v_fvars_1229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 6, v_mvars_1230_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 7, v_lmap_1231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 8, v_emap_1232_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1250_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1233_,
                    );
                    v___x_1248_ = v_reuseFailAlloc_1250_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1249_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1249_, 0, v___x_1242_);
                leanh::lean_ctor_set(v___x_1249_, 1, v___x_1248_);
                return v___x_1249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AbstractMVars_mkFreshFVarId(
    mut v_a_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1255_ = l_Lean_Meta_AbstractMVars_mkFreshId(v_a_1254_);
                v_fst_1256_ = leanh::lean_ctor_get(v___x_1255_, 0);
                v_snd_1257_ = leanh::lean_ctor_get(v___x_1255_, 1);
                v_isSharedCheck_1264_ = (!leanh::lean_is_exclusive(v___x_1255_)) as u8;
                if v_isSharedCheck_1264_ == 0 {
                    v___x_1259_ = v___x_1255_;
                    v_isShared_1260_ = v_isSharedCheck_1264_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1257_);
                    leanh::lean_inc(v_fst_1256_);
                    leanh::lean_dec(v___x_1255_);
                    v___x_1259_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1263_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_fst_1256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_snd_1257_);
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
    mut v_x_1265_: *mut leanh::LeanObject,
    mut v_x_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1266_) == 0 {
                    return v_x_1265_;
                } else {
                    v_key_1267_ = leanh::lean_ctor_get(v_x_1266_, 0);
                    v_value_1268_ = leanh::lean_ctor_get(v_x_1266_, 1);
                    v_tail_1269_ = leanh::lean_ctor_get(v_x_1266_, 2);
                    v_isSharedCheck_1292_ = (!leanh::lean_is_exclusive(v_x_1266_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1271_ = v_x_1266_;
                        v_isShared_1272_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1269_);
                        leanh::lean_inc(v_value_1268_);
                        leanh::lean_inc(v_key_1267_);
                        leanh::lean_dec(v_x_1266_);
                        v___x_1271_ = leanh::lean_box(0);
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
                leanh::lean_inc(v___x_1286_);
                if v_isShared_1272_ == 0 {
                    leanh::lean_ctor_set(v___x_1271_, 2, v___x_1286_);
                    v___x_1288_ = v___x_1271_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_key_1267_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_value_1268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 2, v___x_1286_);
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
    mut v_i_1293_: *mut leanh::LeanObject,
    mut v_source_1294_: *mut leanh::LeanObject,
    mut v_target_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v_es_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1296_ = lean_array_get_size(v_source_1294_);
                v___x_1297_ = lean_nat_dec_lt(v_i_1293_, v___x_1296_);
                if v___x_1297_ == 0 {
                    leanh::lean_dec_ref(v_source_1294_);
                    leanh::lean_dec(v_i_1293_);
                    return v_target_1295_;
                } else {
                    v_es_1298_ = lean_array_fget(v_source_1294_, v_i_1293_);
                    v___x_1299_ = leanh::lean_box(0);
                    v_source_1300_ = lean_array_fset(v_source_1294_, v_i_1293_, v___x_1299_);
                    v_target_1301_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1295_, v_es_1298_);
                    v___x_1302_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1303_ = lean_nat_add(v_i_1293_, v___x_1302_);
                    leanh::lean_dec(v_i_1293_);
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
    mut v_data_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1306_ = lean_array_get_size(v_data_1305_);
    v___x_1307_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1308_ = lean_nat_mul(v___x_1306_, v___x_1307_);
    v___x_1309_ = leanh::lean_unsigned_to_nat(0);
    v___x_1310_ = leanh::lean_box(0);
    v___x_1311_ = lean_mk_array(v_nbuckets_1308_, v___x_1310_);
    v___x_1312_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v___x_1309_, v_data_1305_, v___x_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(
    mut v_a_1313_: *mut leanh::LeanObject,
    mut v_b_1314_: *mut leanh::LeanObject,
    mut v_x_1315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1315_) == 0 {
                    leanh::lean_dec(v_b_1314_);
                    leanh::lean_dec(v_a_1313_);
                    return v_x_1315_;
                } else {
                    v_key_1316_ = leanh::lean_ctor_get(v_x_1315_, 0);
                    v_value_1317_ = leanh::lean_ctor_get(v_x_1315_, 1);
                    v_tail_1318_ = leanh::lean_ctor_get(v_x_1315_, 2);
                    v_isSharedCheck_1330_ = (!leanh::lean_is_exclusive(v_x_1315_)) as u8;
                    if v_isSharedCheck_1330_ == 0 {
                        v___x_1320_ = v_x_1315_;
                        v_isShared_1321_ = v_isSharedCheck_1330_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1318_);
                        leanh::lean_inc(v_value_1317_);
                        leanh::lean_inc(v_key_1316_);
                        leanh::lean_dec(v_x_1315_);
                        v___x_1320_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_1320_, 2, v___x_1323_);
                        v___x_1325_ = v___x_1320_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1326_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_key_1316_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_value_1317_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 2, v___x_1323_);
                        v___x_1325_ = v_reuseFailAlloc_1326_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1317_);
                    leanh::lean_dec(v_key_1316_);
                    if v_isShared_1321_ == 0 {
                        leanh::lean_ctor_set(v___x_1320_, 1, v_b_1314_);
                        leanh::lean_ctor_set(v___x_1320_, 0, v_a_1313_);
                        v___x_1328_ = v___x_1320_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1329_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1313_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_b_1314_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_tail_1318_);
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
    mut v_a_1331_: *mut leanh::LeanObject,
    mut v_x_1332_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1333_: u8 = 0;
    let mut v_key_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1332_) == 0 {
                    v___x_1333_ = 0;
                    return v___x_1333_;
                } else {
                    v_key_1334_ = leanh::lean_ctor_get(v_x_1332_, 0);
                    v_tail_1335_ = leanh::lean_ctor_get(v_x_1332_, 2);
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
    mut v_a_1338_: *mut leanh::LeanObject,
    mut v_x_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1340_: u8 = 0;
    let mut v_r_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_1338_, v_x_1339_);
    leanh::lean_dec(v_x_1339_);
    leanh::lean_dec(v_a_1338_);
    v_r_1341_ = leanh::lean_box((v_res_1340_) as usize);
    return v_r_1341_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(
    mut v_m_1342_: *mut leanh::LeanObject,
    mut v_a_1343_: *mut leanh::LeanObject,
    mut v_b_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v_val_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1345_ = leanh::lean_ctor_get(v_m_1342_, 0);
                v_buckets_1346_ = leanh::lean_ctor_get(v_m_1342_, 1);
                v_isSharedCheck_1389_ = (!leanh::lean_is_exclusive(v_m_1342_)) as u8;
                if v_isSharedCheck_1389_ == 0 {
                    v___x_1348_ = v_m_1342_;
                    v_isShared_1349_ = v_isSharedCheck_1389_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1346_);
                    leanh::lean_inc(v_size_1345_);
                    leanh::lean_dec(v_m_1342_);
                    v___x_1348_ = leanh::lean_box(0);
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
                    v___x_1365_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1366_ = lean_nat_add(v_size_1345_, v___x_1365_);
                    leanh::lean_dec(v_size_1345_);
                    leanh::lean_inc(v_bkt_1363_);
                    v___x_1367_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1367_, 0, v_a_1343_);
                    leanh::lean_ctor_set(v___x_1367_, 1, v_b_1344_);
                    leanh::lean_ctor_set(v___x_1367_, 2, v_bkt_1363_);
                    v_buckets_x27_1368_ =
                        lean_array_uset(v_buckets_1346_, v___x_1362_, v___x_1367_);
                    v___x_1369_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1370_ = lean_nat_mul(v_size_x27_1366_, v___x_1369_);
                    v___x_1371_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1372_ = lean_nat_div(v___x_1370_, v___x_1371_);
                    leanh::lean_dec(v___x_1370_);
                    v___x_1373_ = lean_array_get_size(v_buckets_x27_1368_);
                    v___x_1374_ = lean_nat_dec_le(v___x_1372_, v___x_1373_);
                    leanh::lean_dec(v___x_1372_);
                    if v___x_1374_ == 0 {
                        v_val_1375_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_buckets_x27_1368_);
                        if v_isShared_1349_ == 0 {
                            leanh::lean_ctor_set(v___x_1348_, 1, v_val_1375_);
                            leanh::lean_ctor_set(v___x_1348_, 0, v_size_x27_1366_);
                            v___x_1377_ = v___x_1348_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1378_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1378_,
                                0,
                                v_size_x27_1366_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_val_1375_);
                            v___x_1377_ = v_reuseFailAlloc_1378_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1349_ == 0 {
                            leanh::lean_ctor_set(v___x_1348_, 1, v_buckets_x27_1368_);
                            leanh::lean_ctor_set(v___x_1348_, 0, v_size_x27_1366_);
                            v___x_1380_ = v___x_1348_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1381_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1381_,
                                0,
                                v_size_x27_1366_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_1363_);
                    v___x_1382_ = leanh::lean_box(0);
                    v_buckets_x27_1383_ =
                        lean_array_uset(v_buckets_1346_, v___x_1362_, v___x_1382_);
                    v___x_1384_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_1343_, v_b_1344_, v_bkt_1363_);
                    v___x_1385_ = lean_array_uset(v_buckets_x27_1383_, v___x_1362_, v___x_1384_);
                    if v_isShared_1349_ == 0 {
                        leanh::lean_ctor_set(v___x_1348_, 1, v___x_1385_);
                        v___x_1387_ = v___x_1348_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1388_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_size_1345_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1385_);
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
    mut v_a_1390_: *mut leanh::LeanObject,
    mut v_x_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1391_) == 0 {
                    v___x_1392_ = leanh::lean_box(0);
                    return v___x_1392_;
                } else {
                    v_key_1393_ = leanh::lean_ctor_get(v_x_1391_, 0);
                    v_value_1394_ = leanh::lean_ctor_get(v_x_1391_, 1);
                    v_tail_1395_ = leanh::lean_ctor_get(v_x_1391_, 2);
                    v___x_1396_ = l_Lean_instBEqLevelMVarId_beq(v_key_1393_, v_a_1390_);
                    if v___x_1396_ == 0 {
                        v_x_1391_ = v_tail_1395_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1394_);
                        v___x_1398_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1398_, 0, v_value_1394_);
                        return v___x_1398_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg___boxed(
    mut v_a_1399_: *mut leanh::LeanObject,
    mut v_x_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_1399_, v_x_1400_);
    leanh::lean_dec(v_x_1400_);
    leanh::lean_dec(v_a_1399_);
    return v_res_1401_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(
    mut v_m_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1404_ = leanh::lean_ctor_get(v_m_1402_, 1);
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
    mut v_m_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_1420_, v_a_1421_);
    leanh::lean_dec(v_a_1421_);
    leanh::lean_dec_ref(v_m_1420_);
    return v_res_1422_;
}
pub unsafe fn l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(
    mut v_u_1426_: *mut leanh::LeanObject,
    mut v_a_1427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_abstractLevels_1428_: u8 = 0;
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1447_: u8 = 0;
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1458_: u8 = 0;
    let mut v_a_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1469_: u8 = 0;
    let mut v___y_1471_: u8 = 0;
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: usize = 0;
    let mut v___x_1481_: usize = 0;
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: u8 = 0;
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v_a_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___y_1499_: u8 = 0;
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: usize = 0;
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: usize = 0;
    let mut v___x_1513_: u8 = 0;
    let mut v_isSharedCheck_1514_: u8 = 0;
    let mut v_a_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1535_: u8 = 0;
    let mut v_unused_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_abstractLevels_1428_ = leanh::lean_ctor_get_uint8(
                    v_a_1427_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                );
                if v_abstractLevels_1428_ == 0 {
                    v___x_1429_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1429_, 0, v_u_1426_);
                    leanh::lean_ctor_set(v___x_1429_, 1, v_a_1427_);
                    return v___x_1429_;
                } else {
                    v_ngen_1430_ = leanh::lean_ctor_get(v_a_1427_, 0);
                    v_lctx_1431_ = leanh::lean_ctor_get(v_a_1427_, 1);
                    v_mctx_1432_ = leanh::lean_ctor_get(v_a_1427_, 2);
                    v_nextParamIdx_1433_ = leanh::lean_ctor_get(v_a_1427_, 3);
                    v_paramNames_1434_ = leanh::lean_ctor_get(v_a_1427_, 4);
                    v_fvars_1435_ = leanh::lean_ctor_get(v_a_1427_, 5);
                    v_mvars_1436_ = leanh::lean_ctor_get(v_a_1427_, 6);
                    v_lmap_1437_ = leanh::lean_ctor_get(v_a_1427_, 7);
                    v_emap_1438_ = leanh::lean_ctor_get(v_a_1427_, 8);
                    v___x_1439_ = l_Lean_Level_hasMVar(v_u_1426_);
                    if v___x_1439_ == 0 {
                        v___x_1440_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1440_, 0, v_u_1426_);
                        leanh::lean_ctor_set(v___x_1440_, 1, v_a_1427_);
                        return v___x_1440_;
                    } else {
                        match leanh::lean_obj_tag(v_u_1426_) {
                            1 => {
                                v_a_1441_ = leanh::lean_ctor_get(v_u_1426_, 0);
                                leanh::lean_inc(v_a_1441_);
                                v___x_1442_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1441_, v_a_1427_);
                                v_fst_1443_ = leanh::lean_ctor_get(v___x_1442_, 0);
                                v_snd_1444_ = leanh::lean_ctor_get(v___x_1442_, 1);
                                v_isSharedCheck_1458_ =
                                    (!leanh::lean_is_exclusive(v___x_1442_)) as u8;
                                if v_isSharedCheck_1458_ == 0 {
                                    v___x_1446_ = v___x_1442_;
                                    v_isShared_1447_ = v_isSharedCheck_1458_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_snd_1444_);
                                    leanh::lean_inc(v_fst_1443_);
                                    leanh::lean_dec(v___x_1442_);
                                    v___x_1446_ = leanh::lean_box(0);
                                    v_isShared_1447_ = v_isSharedCheck_1458_;
                                    state = 1;
                                    continue;
                                }
                            }
                            2 => {
                                v_a_1459_ = leanh::lean_ctor_get(v_u_1426_, 0);
                                v_a_1460_ = leanh::lean_ctor_get(v_u_1426_, 1);
                                leanh::lean_inc(v_a_1459_);
                                v___x_1461_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1459_, v_a_1427_);
                                v_fst_1462_ = leanh::lean_ctor_get(v___x_1461_, 0);
                                leanh::lean_inc(v_fst_1462_);
                                v_snd_1463_ = leanh::lean_ctor_get(v___x_1461_, 1);
                                leanh::lean_inc(v_snd_1463_);
                                leanh::lean_dec_ref(v___x_1461_);
                                leanh::lean_inc(v_a_1460_);
                                v___x_1464_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1460_, v_snd_1463_);
                                v_fst_1465_ = leanh::lean_ctor_get(v___x_1464_, 0);
                                v_snd_1466_ = leanh::lean_ctor_get(v___x_1464_, 1);
                                v_isSharedCheck_1486_ =
                                    (!leanh::lean_is_exclusive(v___x_1464_)) as u8;
                                if v_isSharedCheck_1486_ == 0 {
                                    v___x_1468_ = v___x_1464_;
                                    v_isShared_1469_ = v_isSharedCheck_1486_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_snd_1466_);
                                    leanh::lean_inc(v_fst_1465_);
                                    leanh::lean_dec(v___x_1464_);
                                    v___x_1468_ = leanh::lean_box(0);
                                    v_isShared_1469_ = v_isSharedCheck_1486_;
                                    state = 4;
                                    continue;
                                }
                            }
                            3 => {
                                v_a_1487_ = leanh::lean_ctor_get(v_u_1426_, 0);
                                v_a_1488_ = leanh::lean_ctor_get(v_u_1426_, 1);
                                leanh::lean_inc(v_a_1487_);
                                v___x_1489_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1487_, v_a_1427_);
                                v_fst_1490_ = leanh::lean_ctor_get(v___x_1489_, 0);
                                leanh::lean_inc(v_fst_1490_);
                                v_snd_1491_ = leanh::lean_ctor_get(v___x_1489_, 1);
                                leanh::lean_inc(v_snd_1491_);
                                leanh::lean_dec_ref(v___x_1489_);
                                leanh::lean_inc(v_a_1488_);
                                v___x_1492_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_1488_, v_snd_1491_);
                                v_fst_1493_ = leanh::lean_ctor_get(v___x_1492_, 0);
                                v_snd_1494_ = leanh::lean_ctor_get(v___x_1492_, 1);
                                v_isSharedCheck_1514_ =
                                    (!leanh::lean_is_exclusive(v___x_1492_)) as u8;
                                if v_isSharedCheck_1514_ == 0 {
                                    v___x_1496_ = v___x_1492_;
                                    v_isShared_1497_ = v_isSharedCheck_1514_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_snd_1494_);
                                    leanh::lean_inc(v_fst_1493_);
                                    leanh::lean_dec(v___x_1492_);
                                    v___x_1496_ = leanh::lean_box(0);
                                    v_isShared_1497_ = v_isSharedCheck_1514_;
                                    state = 8;
                                    continue;
                                }
                            }
                            5 => {
                                v_a_1515_ = leanh::lean_ctor_get(v_u_1426_, 0);
                                v_depth_1516_ = leanh::lean_ctor_get(v_mctx_1432_, 0);
                                leanh::lean_inc(v_a_1515_);
                                v___x_1517_ =
                                    l_Lean_MetavarContext_getLevelDepth(v_mctx_1432_, v_a_1515_);
                                v___x_1518_ = lean_nat_dec_eq(v___x_1517_, v_depth_1516_);
                                leanh::lean_dec(v___x_1517_);
                                if v___x_1518_ == 0 {
                                    v___x_1519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1519_, 0, v_u_1426_);
                                    leanh::lean_ctor_set(v___x_1519_, 1, v_a_1427_);
                                    return v___x_1519_;
                                } else {
                                    leanh::lean_inc(v_a_1515_);
                                    leanh::lean_dec_ref_known(v_u_1426_, 1);
                                    v___x_1520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_lmap_1437_, v_a_1515_);
                                    if leanh::lean_obj_tag(v___x_1520_) == 0 {
                                        leanh::lean_inc_ref(v_emap_1438_);
                                        leanh::lean_inc_ref(v_lmap_1437_);
                                        leanh::lean_inc_ref(v_mvars_1436_);
                                        leanh::lean_inc_ref(v_fvars_1435_);
                                        leanh::lean_inc_ref(v_paramNames_1434_);
                                        leanh::lean_inc(v_nextParamIdx_1433_);
                                        leanh::lean_inc_ref(v_mctx_1432_);
                                        leanh::lean_inc_ref(v_lctx_1431_);
                                        leanh::lean_inc_ref(v_ngen_1430_);
                                        v_isSharedCheck_1535_ =
                                            (!leanh::lean_is_exclusive(v_a_1427_)) as u8;
                                        if v_isSharedCheck_1535_ == 0 {
                                            v_unused_1536_ =
                                                leanh::lean_ctor_get(v_a_1427_, 8);
                                            leanh::lean_dec(v_unused_1536_);
                                            v_unused_1537_ =
                                                leanh::lean_ctor_get(v_a_1427_, 7);
                                            leanh::lean_dec(v_unused_1537_);
                                            v_unused_1538_ =
                                                leanh::lean_ctor_get(v_a_1427_, 6);
                                            leanh::lean_dec(v_unused_1538_);
                                            v_unused_1539_ =
                                                leanh::lean_ctor_get(v_a_1427_, 5);
                                            leanh::lean_dec(v_unused_1539_);
                                            v_unused_1540_ =
                                                leanh::lean_ctor_get(v_a_1427_, 4);
                                            leanh::lean_dec(v_unused_1540_);
                                            v_unused_1541_ =
                                                leanh::lean_ctor_get(v_a_1427_, 3);
                                            leanh::lean_dec(v_unused_1541_);
                                            v_unused_1542_ =
                                                leanh::lean_ctor_get(v_a_1427_, 2);
                                            leanh::lean_dec(v_unused_1542_);
                                            v_unused_1543_ =
                                                leanh::lean_ctor_get(v_a_1427_, 1);
                                            leanh::lean_dec(v_unused_1543_);
                                            v_unused_1544_ =
                                                leanh::lean_ctor_get(v_a_1427_, 0);
                                            leanh::lean_dec(v_unused_1544_);
                                            v___x_1522_ = v_a_1427_;
                                            v_isShared_1523_ = v_isSharedCheck_1535_;
                                            state = 12;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v_a_1427_);
                                            v___x_1522_ = leanh::lean_box(0);
                                            v_isShared_1523_ = v_isSharedCheck_1535_;
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_1515_);
                                        v_val_1545_ = leanh::lean_ctor_get(v___x_1520_, 0);
                                        leanh::lean_inc(v_val_1545_);
                                        leanh::lean_dec_ref_known(v___x_1520_, 1);
                                        v___x_1546_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1546_, 0, v_val_1545_);
                                        leanh::lean_ctor_set(v___x_1546_, 1, v_a_1427_);
                                        return v___x_1546_;
                                    }
                                }
                            }
                            _ => {
                                v___x_1547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1547_, 0, v_u_1426_);
                                leanh::lean_ctor_set(v___x_1547_, 1, v_a_1427_);
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
                    leanh::lean_dec_ref_known(v_u_1426_, 1);
                    v___x_1451_ = l_Lean_Level_succ___override(v_fst_1443_);
                    if v_isShared_1447_ == 0 {
                        leanh::lean_ctor_set(v___x_1446_, 0, v___x_1451_);
                        v___x_1453_ = v___x_1446_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1454_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_snd_1444_);
                        v___x_1453_ = v_reuseFailAlloc_1454_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1443_);
                    if v_isShared_1447_ == 0 {
                        leanh::lean_ctor_set(v___x_1446_, 0, v_u_1426_);
                        v___x_1456_ = v___x_1446_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1457_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_u_1426_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_snd_1444_);
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
                    leanh::lean_dec_ref_known(v_u_1426_, 2);
                    v___x_1472_ = l_Lean_mkLevelMax_x27(v_fst_1462_, v_fst_1465_);
                    if v_isShared_1469_ == 0 {
                        leanh::lean_ctor_set(v___x_1468_, 0, v___x_1472_);
                        v___x_1474_ = v___x_1468_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1475_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_snd_1466_);
                        v___x_1474_ = v_reuseFailAlloc_1475_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_1476_ = l_Lean_simpLevelMax_x27(v_fst_1462_, v_fst_1465_, v_u_1426_);
                    leanh::lean_dec_ref_known(v_u_1426_, 2);
                    leanh::lean_dec(v_fst_1465_);
                    leanh::lean_dec(v_fst_1462_);
                    if v_isShared_1469_ == 0 {
                        leanh::lean_ctor_set(v___x_1468_, 0, v___x_1476_);
                        v___x_1478_ = v___x_1468_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1479_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_snd_1466_);
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
                    leanh::lean_dec_ref_known(v_u_1426_, 2);
                    v___x_1500_ = l_Lean_mkLevelIMax_x27(v_fst_1490_, v_fst_1493_);
                    if v_isShared_1497_ == 0 {
                        leanh::lean_ctor_set(v___x_1496_, 0, v___x_1500_);
                        v___x_1502_ = v___x_1496_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1503_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_snd_1494_);
                        v___x_1502_ = v_reuseFailAlloc_1503_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_1504_ = l_Lean_simpLevelIMax_x27(v_fst_1490_, v_fst_1493_, v_u_1426_);
                    leanh::lean_dec_ref_known(v_u_1426_, 2);
                    if v_isShared_1497_ == 0 {
                        leanh::lean_ctor_set(v___x_1496_, 0, v___x_1504_);
                        v___x_1506_ = v___x_1496_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_snd_1494_);
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
                leanh::lean_inc(v_nextParamIdx_1433_);
                v___x_1525_ = l_Lean_Name_num___override(v___x_1524_, v_nextParamIdx_1433_);
                leanh::lean_inc(v___x_1525_);
                v___x_1526_ = l_Lean_mkLevelParam(v___x_1525_);
                v___x_1527_ = leanh::lean_unsigned_to_nat(1);
                v___x_1528_ = lean_nat_add(v_nextParamIdx_1433_, v___x_1527_);
                leanh::lean_dec(v_nextParamIdx_1433_);
                v___x_1529_ = lean_array_push(v_paramNames_1434_, v___x_1525_);
                leanh::lean_inc(v___x_1526_);
                v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_lmap_1437_, v_a_1515_, v___x_1526_);
                if v_isShared_1523_ == 0 {
                    leanh::lean_ctor_set(v___x_1522_, 7, v___x_1530_);
                    leanh::lean_ctor_set(v___x_1522_, 4, v___x_1529_);
                    leanh::lean_ctor_set(v___x_1522_, 3, v___x_1528_);
                    v___x_1532_ = v___x_1522_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1534_ = leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_ngen_1430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_lctx_1431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_mctx_1432_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 3, v___x_1528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 4, v___x_1529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 5, v_fvars_1435_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 6, v_mvars_1436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 7, v___x_1530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 8, v_emap_1438_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1534_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1428_,
                    );
                    v___x_1532_ = v_reuseFailAlloc_1534_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1533_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1533_, 0, v___x_1526_);
                leanh::lean_ctor_set(v___x_1533_, 1, v___x_1532_);
                return v___x_1533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(
    mut v_00_u03b2_1548_: *mut leanh::LeanObject,
    mut v_m_1549_: *mut leanh::LeanObject,
    mut v_a_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_1549_, v_a_1550_);
    return v___x_1551_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(
    mut v_00_u03b2_1552_: *mut leanh::LeanObject,
    mut v_m_1553_: *mut leanh::LeanObject,
    mut v_a_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(v_00_u03b2_1552_, v_m_1553_, v_a_1554_);
    leanh::lean_dec(v_a_1554_);
    leanh::lean_dec_ref(v_m_1553_);
    return v_res_1555_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(
    mut v_00_u03b2_1556_: *mut leanh::LeanObject,
    mut v_m_1557_: *mut leanh::LeanObject,
    mut v_a_1558_: *mut leanh::LeanObject,
    mut v_b_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_1557_, v_a_1558_, v_b_1559_);
    return v___x_1560_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(
    mut v_00_u03b2_1561_: *mut leanh::LeanObject,
    mut v_a_1562_: *mut leanh::LeanObject,
    mut v_x_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_1562_, v_x_1563_);
    return v___x_1564_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_1565_: *mut leanh::LeanObject,
    mut v_a_1566_: *mut leanh::LeanObject,
    mut v_x_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(v_00_u03b2_1565_, v_a_1566_, v_x_1567_);
    leanh::lean_dec(v_x_1567_);
    leanh::lean_dec(v_a_1566_);
    return v_res_1568_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(
    mut v_00_u03b2_1569_: *mut leanh::LeanObject,
    mut v_a_1570_: *mut leanh::LeanObject,
    mut v_x_1571_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1572_: u8 = 0;
    v___x_1572_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_1570_, v_x_1571_);
    return v___x_1572_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(
    mut v_00_u03b2_1573_: *mut leanh::LeanObject,
    mut v_a_1574_: *mut leanh::LeanObject,
    mut v_x_1575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1576_: u8 = 0;
    let mut v_r_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(v_00_u03b2_1573_, v_a_1574_, v_x_1575_);
    leanh::lean_dec(v_x_1575_);
    leanh::lean_dec(v_a_1574_);
    v_r_1577_ = leanh::lean_box((v_res_1576_) as usize);
    return v_r_1577_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3(
    mut v_00_u03b2_1578_: *mut leanh::LeanObject,
    mut v_data_1579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_data_1579_);
    return v___x_1580_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4(
    mut v_00_u03b2_1581_: *mut leanh::LeanObject,
    mut v_a_1582_: *mut leanh::LeanObject,
    mut v_b_1583_: *mut leanh::LeanObject,
    mut v_x_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_1582_, v_b_1583_, v_x_1584_);
    return v___x_1585_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1586_: *mut leanh::LeanObject,
    mut v_i_1587_: *mut leanh::LeanObject,
    mut v_source_1588_: *mut leanh::LeanObject,
    mut v_target_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1590_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v_i_1587_, v_source_1588_, v_target_1589_);
    return v___x_1590_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1591_: *mut leanh::LeanObject,
    mut v_x_1592_: *mut leanh::LeanObject,
    mut v_x_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1592_, v_x_1593_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(
    mut v_e_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1597_: u8 = 0;
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1608_: u8 = 0;
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1617_: u8 = 0;
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1597_ = l_Lean_Expr_hasMVar(v_e_1595_);
                if v___x_1597_ == 0 {
                    v___x_1598_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1598_, 0, v_e_1595_);
                    leanh::lean_ctor_set(v___x_1598_, 1, v___y_1596_);
                    return v___x_1598_;
                } else {
                    v_ngen_1599_ = leanh::lean_ctor_get(v___y_1596_, 0);
                    v_lctx_1600_ = leanh::lean_ctor_get(v___y_1596_, 1);
                    v_mctx_1601_ = leanh::lean_ctor_get(v___y_1596_, 2);
                    v_nextParamIdx_1602_ = leanh::lean_ctor_get(v___y_1596_, 3);
                    v_paramNames_1603_ = leanh::lean_ctor_get(v___y_1596_, 4);
                    v_fvars_1604_ = leanh::lean_ctor_get(v___y_1596_, 5);
                    v_mvars_1605_ = leanh::lean_ctor_get(v___y_1596_, 6);
                    v_lmap_1606_ = leanh::lean_ctor_get(v___y_1596_, 7);
                    v_emap_1607_ = leanh::lean_ctor_get(v___y_1596_, 8);
                    v_abstractLevels_1608_ = leanh::lean_ctor_get_uint8(
                        v___y_1596_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                    );
                    v_isSharedCheck_1625_ = (!leanh::lean_is_exclusive(v___y_1596_)) as u8;
                    if v_isSharedCheck_1625_ == 0 {
                        v___x_1610_ = v___y_1596_;
                        v_isShared_1611_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_emap_1607_);
                        leanh::lean_inc(v_lmap_1606_);
                        leanh::lean_inc(v_mvars_1605_);
                        leanh::lean_inc(v_fvars_1604_);
                        leanh::lean_inc(v_paramNames_1603_);
                        leanh::lean_inc(v_nextParamIdx_1602_);
                        leanh::lean_inc(v_mctx_1601_);
                        leanh::lean_inc(v_lctx_1600_);
                        leanh::lean_inc(v_ngen_1599_);
                        leanh::lean_dec(v___y_1596_);
                        v___x_1610_ = leanh::lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1612_ = l_Lean_instantiateMVarsCore(v_mctx_1601_, v_e_1595_);
                v_fst_1613_ = leanh::lean_ctor_get(v___x_1612_, 0);
                v_snd_1614_ = leanh::lean_ctor_get(v___x_1612_, 1);
                v_isSharedCheck_1624_ = (!leanh::lean_is_exclusive(v___x_1612_)) as u8;
                if v_isSharedCheck_1624_ == 0 {
                    v___x_1616_ = v___x_1612_;
                    v_isShared_1617_ = v_isSharedCheck_1624_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1614_);
                    leanh::lean_inc(v_fst_1613_);
                    leanh::lean_dec(v___x_1612_);
                    v___x_1616_ = leanh::lean_box(0);
                    v_isShared_1617_ = v_isSharedCheck_1624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1611_ == 0 {
                    leanh::lean_ctor_set(v___x_1610_, 2, v_snd_1614_);
                    v___x_1619_ = v___x_1610_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1623_ = leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_ngen_1599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_lctx_1600_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_snd_1614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_nextParamIdx_1602_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 4, v_paramNames_1603_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 5, v_fvars_1604_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 6, v_mvars_1605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 7, v_lmap_1606_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 8, v_emap_1607_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1623_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1608_,
                    );
                    v___x_1619_ = v_reuseFailAlloc_1623_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1617_ == 0 {
                    leanh::lean_ctor_set(v___x_1616_, 1, v___x_1619_);
                    v___x_1621_ = v___x_1616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1622_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_fst_1613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1619_);
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
    mut v_a_1626_: *mut leanh::LeanObject,
    mut v_x_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1627_) == 0 {
                    v___x_1628_ = leanh::lean_box(0);
                    return v___x_1628_;
                } else {
                    v_key_1629_ = leanh::lean_ctor_get(v_x_1627_, 0);
                    v_value_1630_ = leanh::lean_ctor_get(v_x_1627_, 1);
                    v_tail_1631_ = leanh::lean_ctor_get(v_x_1627_, 2);
                    v___x_1632_ = l_Lean_instBEqMVarId_beq(v_key_1629_, v_a_1626_);
                    if v___x_1632_ == 0 {
                        v_x_1627_ = v_tail_1631_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1630_);
                        v___x_1634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1634_, 0, v_value_1630_);
                        return v___x_1634_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_x_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_1635_, v_x_1636_);
    leanh::lean_dec(v_x_1636_);
    leanh::lean_dec(v_a_1635_);
    return v_res_1637_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(
    mut v_m_1638_: *mut leanh::LeanObject,
    mut v_a_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1640_ = leanh::lean_ctor_get(v_m_1638_, 1);
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
    mut v_m_1656_: *mut leanh::LeanObject,
    mut v_a_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_1656_, v_a_1657_);
    leanh::lean_dec(v_a_1657_);
    leanh::lean_dec_ref(v_m_1656_);
    return v_res_1658_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(
    mut v_a_1659_: *mut leanh::LeanObject,
    mut v_x_1660_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1661_: u8 = 0;
    let mut v_key_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1660_) == 0 {
                    v___x_1661_ = 0;
                    return v___x_1661_;
                } else {
                    v_key_1662_ = leanh::lean_ctor_get(v_x_1660_, 0);
                    v_tail_1663_ = leanh::lean_ctor_get(v_x_1660_, 2);
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
    mut v_a_1666_: *mut leanh::LeanObject,
    mut v_x_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1668_: u8 = 0;
    let mut v_r_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_1666_, v_x_1667_);
    leanh::lean_dec(v_x_1667_);
    leanh::lean_dec(v_a_1666_);
    v_r_1669_ = leanh::lean_box((v_res_1668_) as usize);
    return v_r_1669_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(
    mut v_a_1670_: *mut leanh::LeanObject,
    mut v_b_1671_: *mut leanh::LeanObject,
    mut v_x_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1672_) == 0 {
                    leanh::lean_dec(v_b_1671_);
                    leanh::lean_dec(v_a_1670_);
                    return v_x_1672_;
                } else {
                    v_key_1673_ = leanh::lean_ctor_get(v_x_1672_, 0);
                    v_value_1674_ = leanh::lean_ctor_get(v_x_1672_, 1);
                    v_tail_1675_ = leanh::lean_ctor_get(v_x_1672_, 2);
                    v_isSharedCheck_1687_ = (!leanh::lean_is_exclusive(v_x_1672_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1677_ = v_x_1672_;
                        v_isShared_1678_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1675_);
                        leanh::lean_inc(v_value_1674_);
                        leanh::lean_inc(v_key_1673_);
                        leanh::lean_dec(v_x_1672_);
                        v___x_1677_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_1677_, 2, v___x_1680_);
                        v___x_1682_ = v___x_1677_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1683_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_key_1673_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_value_1674_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 2, v___x_1680_);
                        v___x_1682_ = v_reuseFailAlloc_1683_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1674_);
                    leanh::lean_dec(v_key_1673_);
                    if v_isShared_1678_ == 0 {
                        leanh::lean_ctor_set(v___x_1677_, 1, v_b_1671_);
                        leanh::lean_ctor_set(v___x_1677_, 0, v_a_1670_);
                        v___x_1685_ = v___x_1677_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1686_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1670_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_b_1671_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_tail_1675_);
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
    mut v_x_1688_: *mut leanh::LeanObject,
    mut v_x_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1689_) == 0 {
                    return v_x_1688_;
                } else {
                    v_key_1690_ = leanh::lean_ctor_get(v_x_1689_, 0);
                    v_value_1691_ = leanh::lean_ctor_get(v_x_1689_, 1);
                    v_tail_1692_ = leanh::lean_ctor_get(v_x_1689_, 2);
                    v_isSharedCheck_1715_ = (!leanh::lean_is_exclusive(v_x_1689_)) as u8;
                    if v_isSharedCheck_1715_ == 0 {
                        v___x_1694_ = v_x_1689_;
                        v_isShared_1695_ = v_isSharedCheck_1715_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1692_);
                        leanh::lean_inc(v_value_1691_);
                        leanh::lean_inc(v_key_1690_);
                        leanh::lean_dec(v_x_1689_);
                        v___x_1694_ = leanh::lean_box(0);
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
                leanh::lean_inc(v___x_1709_);
                if v_isShared_1695_ == 0 {
                    leanh::lean_ctor_set(v___x_1694_, 2, v___x_1709_);
                    v___x_1711_ = v___x_1694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_key_1690_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_value_1691_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 2, v___x_1709_);
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
    mut v_i_1716_: *mut leanh::LeanObject,
    mut v_source_1717_: *mut leanh::LeanObject,
    mut v_target_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v_es_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1719_ = lean_array_get_size(v_source_1717_);
                v___x_1720_ = lean_nat_dec_lt(v_i_1716_, v___x_1719_);
                if v___x_1720_ == 0 {
                    leanh::lean_dec_ref(v_source_1717_);
                    leanh::lean_dec(v_i_1716_);
                    return v_target_1718_;
                } else {
                    v_es_1721_ = lean_array_fget(v_source_1717_, v_i_1716_);
                    v___x_1722_ = leanh::lean_box(0);
                    v_source_1723_ = lean_array_fset(v_source_1717_, v_i_1716_, v___x_1722_);
                    v_target_1724_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_target_1718_, v_es_1721_);
                    v___x_1725_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1726_ = lean_nat_add(v_i_1716_, v___x_1725_);
                    leanh::lean_dec(v_i_1716_);
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
    mut v_data_1728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1729_ = lean_array_get_size(v_data_1728_);
    v___x_1730_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1731_ = lean_nat_mul(v___x_1729_, v___x_1730_);
    v___x_1732_ = leanh::lean_unsigned_to_nat(0);
    v___x_1733_ = leanh::lean_box(0);
    v___x_1734_ = lean_mk_array(v_nbuckets_1731_, v___x_1733_);
    v___x_1735_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v___x_1732_, v_data_1728_, v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(
    mut v_m_1736_: *mut leanh::LeanObject,
    mut v_a_1737_: *mut leanh::LeanObject,
    mut v_b_1738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v_val_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1739_ = leanh::lean_ctor_get(v_m_1736_, 0);
                v_buckets_1740_ = leanh::lean_ctor_get(v_m_1736_, 1);
                v_isSharedCheck_1783_ = (!leanh::lean_is_exclusive(v_m_1736_)) as u8;
                if v_isSharedCheck_1783_ == 0 {
                    v___x_1742_ = v_m_1736_;
                    v_isShared_1743_ = v_isSharedCheck_1783_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1740_);
                    leanh::lean_inc(v_size_1739_);
                    leanh::lean_dec(v_m_1736_);
                    v___x_1742_ = leanh::lean_box(0);
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
                    v___x_1759_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1760_ = lean_nat_add(v_size_1739_, v___x_1759_);
                    leanh::lean_dec(v_size_1739_);
                    leanh::lean_inc(v_bkt_1757_);
                    v___x_1761_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1761_, 0, v_a_1737_);
                    leanh::lean_ctor_set(v___x_1761_, 1, v_b_1738_);
                    leanh::lean_ctor_set(v___x_1761_, 2, v_bkt_1757_);
                    v_buckets_x27_1762_ =
                        lean_array_uset(v_buckets_1740_, v___x_1756_, v___x_1761_);
                    v___x_1763_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1764_ = lean_nat_mul(v_size_x27_1760_, v___x_1763_);
                    v___x_1765_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1766_ = lean_nat_div(v___x_1764_, v___x_1765_);
                    leanh::lean_dec(v___x_1764_);
                    v___x_1767_ = lean_array_get_size(v_buckets_x27_1762_);
                    v___x_1768_ = lean_nat_dec_le(v___x_1766_, v___x_1767_);
                    leanh::lean_dec(v___x_1766_);
                    if v___x_1768_ == 0 {
                        v_val_1769_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_buckets_x27_1762_);
                        if v_isShared_1743_ == 0 {
                            leanh::lean_ctor_set(v___x_1742_, 1, v_val_1769_);
                            leanh::lean_ctor_set(v___x_1742_, 0, v_size_x27_1760_);
                            v___x_1771_ = v___x_1742_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1772_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1772_,
                                0,
                                v_size_x27_1760_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_val_1769_);
                            v___x_1771_ = v_reuseFailAlloc_1772_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1743_ == 0 {
                            leanh::lean_ctor_set(v___x_1742_, 1, v_buckets_x27_1762_);
                            leanh::lean_ctor_set(v___x_1742_, 0, v_size_x27_1760_);
                            v___x_1774_ = v___x_1742_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1775_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1775_,
                                0,
                                v_size_x27_1760_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_1757_);
                    v___x_1776_ = leanh::lean_box(0);
                    v_buckets_x27_1777_ =
                        lean_array_uset(v_buckets_1740_, v___x_1756_, v___x_1776_);
                    v___x_1778_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_1737_, v_b_1738_, v_bkt_1757_);
                    v___x_1779_ = lean_array_uset(v_buckets_x27_1777_, v___x_1756_, v___x_1778_);
                    if v_isShared_1743_ == 0 {
                        leanh::lean_ctor_set(v___x_1742_, 1, v___x_1779_);
                        v___x_1781_ = v___x_1742_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1782_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_size_1739_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1779_);
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
    mut v_x_1784_: *mut leanh::LeanObject,
    mut v_x_1785_: *mut leanh::LeanObject,
    mut v___y_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1784_) == 0 {
                    v___x_1787_ = l_List_reverse___redArg(v_x_1785_);
                    v___x_1788_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1788_, 0, v___x_1787_);
                    leanh::lean_ctor_set(v___x_1788_, 1, v___y_1786_);
                    return v___x_1788_;
                } else {
                    v_head_1789_ = leanh::lean_ctor_get(v_x_1784_, 0);
                    v_tail_1790_ = leanh::lean_ctor_get(v_x_1784_, 1);
                    v_isSharedCheck_1801_ = (!leanh::lean_is_exclusive(v_x_1784_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1792_ = v_x_1784_;
                        v_isShared_1793_ = v_isSharedCheck_1801_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1790_);
                        leanh::lean_inc(v_head_1789_);
                        leanh::lean_dec(v_x_1784_);
                        v___x_1792_ = leanh::lean_box(0);
                        v_isShared_1793_ = v_isSharedCheck_1801_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1794_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_head_1789_, v___y_1786_);
                v_fst_1795_ = leanh::lean_ctor_get(v___x_1794_, 0);
                leanh::lean_inc(v_fst_1795_);
                v_snd_1796_ = leanh::lean_ctor_get(v___x_1794_, 1);
                leanh::lean_inc(v_snd_1796_);
                leanh::lean_dec_ref(v___x_1794_);
                if v_isShared_1793_ == 0 {
                    leanh::lean_ctor_set(v___x_1792_, 1, v_x_1785_);
                    leanh::lean_ctor_set(v___x_1792_, 0, v_fst_1795_);
                    v___x_1798_ = v___x_1792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_fst_1795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_x_1785_);
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
    mut v_e_1805_: *mut leanh::LeanObject,
    mut v_a_1806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextParamIdx_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmap_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_emap_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractLevels_1844_: u8 = 0;
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut v___x_1861_: u8 = 0;
    let mut v_fvars_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_val_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: usize = 0;
    let mut v___x_1878_: u8 = 0;
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_declName_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_fn_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___y_1917_: u8 = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: usize = 0;
    let mut v___x_1926_: usize = 0;
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: usize = 0;
    let mut v___x_1929_: usize = 0;
    let mut v___x_1930_: u8 = 0;
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v_binderName_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1935_: u8 = 0;
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___y_1946_: u8 = 0;
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: usize = 0;
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: usize = 0;
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: u8 = 0;
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_binderName_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1969_: u8 = 0;
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___y_1980_: u8 = 0;
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: u8 = 0;
    let mut v___x_1996_: usize = 0;
    let mut v___x_1997_: usize = 0;
    let mut v___x_1998_: u8 = 0;
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_declName_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2004_: u8 = 0;
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___y_2018_: u8 = 0;
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: usize = 0;
    let mut v___x_2024_: usize = 0;
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: usize = 0;
    let mut v___x_2034_: usize = 0;
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: usize = 0;
    let mut v___x_2037_: usize = 0;
    let mut v___x_2038_: u8 = 0;
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_data_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2047_: u8 = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: usize = 0;
    let mut v___x_2050_: u8 = 0;
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_typeName_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2067_: u8 = 0;
    let mut v___x_2068_: usize = 0;
    let mut v___x_2069_: usize = 0;
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2078_: u8 = 0;
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1807_ = l_Lean_Expr_hasMVar(v_e_1805_);
                if v___x_1807_ == 0 {
                    v___x_1808_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1808_, 0, v_e_1805_);
                    leanh::lean_ctor_set(v___x_1808_, 1, v_a_1806_);
                    return v___x_1808_;
                } else {
                    match leanh::lean_obj_tag(v_e_1805_) {
                        2 => {
                            v_mvarId_1809_ = leanh::lean_ctor_get(v_e_1805_, 0);
                            v_mctx_1810_ = leanh::lean_ctor_get(v_a_1806_, 2);
                            v_emap_1811_ = leanh::lean_ctor_get(v_a_1806_, 8);
                            leanh::lean_inc(v_mvarId_1809_);
                            v___x_1812_ =
                                l_Lean_MetavarContext_getDecl(v_mctx_1810_, v_mvarId_1809_);
                            v_userName_1813_ = leanh::lean_ctor_get(v___x_1812_, 0);
                            leanh::lean_inc(v_userName_1813_);
                            v_type_1814_ = leanh::lean_ctor_get(v___x_1812_, 2);
                            leanh::lean_inc_ref(v_type_1814_);
                            v_depth_1815_ = leanh::lean_ctor_get(v___x_1812_, 3);
                            leanh::lean_inc(v_depth_1815_);
                            leanh::lean_dec_ref(v___x_1812_);
                            v_depth_1816_ = leanh::lean_ctor_get(v_mctx_1810_, 0);
                            v___x_1817_ = lean_nat_dec_eq(v_depth_1815_, v_depth_1816_);
                            leanh::lean_dec(v_depth_1815_);
                            if v___x_1817_ == 0 {
                                leanh::lean_dec_ref(v_type_1814_);
                                leanh::lean_dec(v_userName_1813_);
                                v___x_1818_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1818_, 0, v_e_1805_);
                                leanh::lean_ctor_set(v___x_1818_, 1, v_a_1806_);
                                return v___x_1818_;
                            } else {
                                leanh::lean_inc(v_mvarId_1809_);
                                v___x_1819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_emap_1811_, v_mvarId_1809_);
                                if leanh::lean_obj_tag(v___x_1819_) == 0 {
                                    v___x_1820_ = l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(v_type_1814_, v_a_1806_);
                                    v_fst_1821_ = leanh::lean_ctor_get(v___x_1820_, 0);
                                    leanh::lean_inc(v_fst_1821_);
                                    v_snd_1822_ = leanh::lean_ctor_get(v___x_1820_, 1);
                                    leanh::lean_inc(v_snd_1822_);
                                    leanh::lean_dec_ref(v___x_1820_);
                                    v___x_1823_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                        v_fst_1821_,
                                        v_snd_1822_,
                                    );
                                    v_fst_1824_ = leanh::lean_ctor_get(v___x_1823_, 0);
                                    leanh::lean_inc(v_fst_1824_);
                                    v_snd_1825_ = leanh::lean_ctor_get(v___x_1823_, 1);
                                    leanh::lean_inc(v_snd_1825_);
                                    leanh::lean_dec_ref(v___x_1823_);
                                    v___x_1826_ =
                                        l_Lean_Meta_AbstractMVars_mkFreshFVarId(v_snd_1825_);
                                    v_fst_1827_ = leanh::lean_ctor_get(v___x_1826_, 0);
                                    v_snd_1828_ = leanh::lean_ctor_get(v___x_1826_, 1);
                                    v_isSharedCheck_1866_ =
                                        (!leanh::lean_is_exclusive(v___x_1826_)) as u8;
                                    if v_isSharedCheck_1866_ == 0 {
                                        v___x_1830_ = v___x_1826_;
                                        v_isShared_1831_ = v_isSharedCheck_1866_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_snd_1828_);
                                        leanh::lean_inc(v_fst_1827_);
                                        leanh::lean_dec(v___x_1826_);
                                        v___x_1830_ = leanh::lean_box(0);
                                        v_isShared_1831_ = v_isSharedCheck_1866_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_type_1814_);
                                    leanh::lean_dec(v_userName_1813_);
                                    leanh::lean_dec_ref_known(v_e_1805_, 1);
                                    leanh::lean_dec(v_mvarId_1809_);
                                    v_val_1867_ = leanh::lean_ctor_get(v___x_1819_, 0);
                                    leanh::lean_inc(v_val_1867_);
                                    leanh::lean_dec_ref_known(v___x_1819_, 1);
                                    v___x_1868_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1868_, 0, v_val_1867_);
                                    leanh::lean_ctor_set(v___x_1868_, 1, v_a_1806_);
                                    return v___x_1868_;
                                }
                            }
                        }
                        3 => {
                            v_u_1869_ = leanh::lean_ctor_get(v_e_1805_, 0);
                            leanh::lean_inc(v_u_1869_);
                            v___x_1870_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_u_1869_, v_a_1806_);
                            v_fst_1871_ = leanh::lean_ctor_get(v___x_1870_, 0);
                            v_snd_1872_ = leanh::lean_ctor_get(v___x_1870_, 1);
                            v_isSharedCheck_1886_ =
                                (!leanh::lean_is_exclusive(v___x_1870_)) as u8;
                            if v_isSharedCheck_1886_ == 0 {
                                v___x_1874_ = v___x_1870_;
                                v_isShared_1875_ = v_isSharedCheck_1886_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1872_);
                                leanh::lean_inc(v_fst_1871_);
                                leanh::lean_dec(v___x_1870_);
                                v___x_1874_ = leanh::lean_box(0);
                                v_isShared_1875_ = v_isSharedCheck_1886_;
                                state = 6;
                                continue;
                            }
                        }
                        4 => {
                            v_declName_1887_ = leanh::lean_ctor_get(v_e_1805_, 0);
                            v_us_1888_ = leanh::lean_ctor_get(v_e_1805_, 1);
                            v___x_1889_ = leanh::lean_box(0);
                            leanh::lean_inc(v_us_1888_);
                            v___x_1890_ = l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(v_us_1888_, v___x_1889_, v_a_1806_);
                            v_fst_1891_ = leanh::lean_ctor_get(v___x_1890_, 0);
                            v_snd_1892_ = leanh::lean_ctor_get(v___x_1890_, 1);
                            v_isSharedCheck_1904_ =
                                (!leanh::lean_is_exclusive(v___x_1890_)) as u8;
                            if v_isSharedCheck_1904_ == 0 {
                                v___x_1894_ = v___x_1890_;
                                v_isShared_1895_ = v_isSharedCheck_1904_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1892_);
                                leanh::lean_inc(v_fst_1891_);
                                leanh::lean_dec(v___x_1890_);
                                v___x_1894_ = leanh::lean_box(0);
                                v_isShared_1895_ = v_isSharedCheck_1904_;
                                state = 9;
                                continue;
                            }
                        }
                        5 => {
                            v_fn_1905_ = leanh::lean_ctor_get(v_e_1805_, 0);
                            v_arg_1906_ = leanh::lean_ctor_get(v_e_1805_, 1);
                            leanh::lean_inc_ref(v_fn_1905_);
                            v___x_1907_ =
                                l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fn_1905_, v_a_1806_);
                            v_fst_1908_ = leanh::lean_ctor_get(v___x_1907_, 0);
                            leanh::lean_inc(v_fst_1908_);
                            v_snd_1909_ = leanh::lean_ctor_get(v___x_1907_, 1);
                            leanh::lean_inc(v_snd_1909_);
                            leanh::lean_dec_ref(v___x_1907_);
                            leanh::lean_inc_ref(v_arg_1906_);
                            v___x_1910_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_arg_1906_,
                                v_snd_1909_,
                            );
                            v_fst_1911_ = leanh::lean_ctor_get(v___x_1910_, 0);
                            v_snd_1912_ = leanh::lean_ctor_get(v___x_1910_, 1);
                            v_isSharedCheck_1931_ =
                                (!leanh::lean_is_exclusive(v___x_1910_)) as u8;
                            if v_isSharedCheck_1931_ == 0 {
                                v___x_1914_ = v___x_1910_;
                                v_isShared_1915_ = v_isSharedCheck_1931_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1912_);
                                leanh::lean_inc(v_fst_1911_);
                                leanh::lean_dec(v___x_1910_);
                                v___x_1914_ = leanh::lean_box(0);
                                v_isShared_1915_ = v_isSharedCheck_1931_;
                                state = 12;
                                continue;
                            }
                        }
                        6 => {
                            v_binderName_1932_ = leanh::lean_ctor_get(v_e_1805_, 0);
                            v_binderType_1933_ = leanh::lean_ctor_get(v_e_1805_, 1);
                            v_body_1934_ = leanh::lean_ctor_get(v_e_1805_, 2);
                            v_binderInfo_1935_ = leanh::lean_ctor_get_uint8(
                                v_e_1805_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            leanh::lean_inc_ref(v_binderType_1933_);
                            v___x_1936_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_binderType_1933_,
                                v_a_1806_,
                            );
                            v_fst_1937_ = leanh::lean_ctor_get(v___x_1936_, 0);
                            leanh::lean_inc(v_fst_1937_);
                            v_snd_1938_ = leanh::lean_ctor_get(v___x_1936_, 1);
                            leanh::lean_inc(v_snd_1938_);
                            leanh::lean_dec_ref(v___x_1936_);
                            leanh::lean_inc_ref(v_body_1934_);
                            v___x_1939_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_body_1934_,
                                v_snd_1938_,
                            );
                            v_fst_1940_ = leanh::lean_ctor_get(v___x_1939_, 0);
                            v_snd_1941_ = leanh::lean_ctor_get(v___x_1939_, 1);
                            v_isSharedCheck_1965_ =
                                (!leanh::lean_is_exclusive(v___x_1939_)) as u8;
                            if v_isSharedCheck_1965_ == 0 {
                                v___x_1943_ = v___x_1939_;
                                v_isShared_1944_ = v_isSharedCheck_1965_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1941_);
                                leanh::lean_inc(v_fst_1940_);
                                leanh::lean_dec(v___x_1939_);
                                v___x_1943_ = leanh::lean_box(0);
                                v_isShared_1944_ = v_isSharedCheck_1965_;
                                state = 16;
                                continue;
                            }
                        }
                        7 => {
                            v_binderName_1966_ = leanh::lean_ctor_get(v_e_1805_, 0);
                            v_binderType_1967_ = leanh::lean_ctor_get(v_e_1805_, 1);
                            v_body_1968_ = leanh::lean_ctor_get(v_e_1805_, 2);
                            v_binderInfo_1969_ = leanh::lean_ctor_get_uint8(
                                v_e_1805_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            leanh::lean_inc_ref(v_binderType_1967_);
                            v___x_1970_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_binderType_1967_,
                                v_a_1806_,
                            );
                            v_fst_1971_ = leanh::lean_ctor_get(v___x_1970_, 0);
                            leanh::lean_inc(v_fst_1971_);
                            v_snd_1972_ = leanh::lean_ctor_get(v___x_1970_, 1);
                            leanh::lean_inc(v_snd_1972_);
                            leanh::lean_dec_ref(v___x_1970_);
                            leanh::lean_inc_ref(v_body_1968_);
                            v___x_1973_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_body_1968_,
                                v_snd_1972_,
                            );
                            v_fst_1974_ = leanh::lean_ctor_get(v___x_1973_, 0);
                            v_snd_1975_ = leanh::lean_ctor_get(v___x_1973_, 1);
                            v_isSharedCheck_1999_ =
                                (!leanh::lean_is_exclusive(v___x_1973_)) as u8;
                            if v_isSharedCheck_1999_ == 0 {
                                v___x_1977_ = v___x_1973_;
                                v_isShared_1978_ = v_isSharedCheck_1999_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1975_);
                                leanh::lean_inc(v_fst_1974_);
                                leanh::lean_dec(v___x_1973_);
                                v___x_1977_ = leanh::lean_box(0);
                                v_isShared_1978_ = v_isSharedCheck_1999_;
                                state = 21;
                                continue;
                            }
                        }
                        8 => {
                            v_declName_2000_ = leanh::lean_ctor_get(v_e_1805_, 0);
                            v_type_2001_ = leanh::lean_ctor_get(v_e_1805_, 1);
                            v_value_2002_ = leanh::lean_ctor_get(v_e_1805_, 2);
                            v_body_2003_ = leanh::lean_ctor_get(v_e_1805_, 3);
                            v_nondep_2004_ = leanh::lean_ctor_get_uint8(
                                v_e_1805_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            leanh::lean_inc_ref(v_type_2001_);
                            v___x_2005_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_type_2001_,
                                v_a_1806_,
                            );
                            v_fst_2006_ = leanh::lean_ctor_get(v___x_2005_, 0);
                            leanh::lean_inc(v_fst_2006_);
                            v_snd_2007_ = leanh::lean_ctor_get(v___x_2005_, 1);
                            leanh::lean_inc(v_snd_2007_);
                            leanh::lean_dec_ref(v___x_2005_);
                            leanh::lean_inc_ref(v_value_2002_);
                            v___x_2008_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_value_2002_,
                                v_snd_2007_,
                            );
                            v_fst_2009_ = leanh::lean_ctor_get(v___x_2008_, 0);
                            leanh::lean_inc(v_fst_2009_);
                            v_snd_2010_ = leanh::lean_ctor_get(v___x_2008_, 1);
                            leanh::lean_inc(v_snd_2010_);
                            leanh::lean_dec_ref(v___x_2008_);
                            leanh::lean_inc_ref(v_body_2003_);
                            v___x_2011_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_body_2003_,
                                v_snd_2010_,
                            );
                            v_fst_2012_ = leanh::lean_ctor_get(v___x_2011_, 0);
                            v_snd_2013_ = leanh::lean_ctor_get(v___x_2011_, 1);
                            v_isSharedCheck_2039_ =
                                (!leanh::lean_is_exclusive(v___x_2011_)) as u8;
                            if v_isSharedCheck_2039_ == 0 {
                                v___x_2015_ = v___x_2011_;
                                v_isShared_2016_ = v_isSharedCheck_2039_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_2013_);
                                leanh::lean_inc(v_fst_2012_);
                                leanh::lean_dec(v___x_2011_);
                                v___x_2015_ = leanh::lean_box(0);
                                v_isShared_2016_ = v_isSharedCheck_2039_;
                                state = 26;
                                continue;
                            }
                        }
                        10 => {
                            v_data_2040_ = leanh::lean_ctor_get(v_e_1805_, 0);
                            v_expr_2041_ = leanh::lean_ctor_get(v_e_1805_, 1);
                            leanh::lean_inc_ref(v_expr_2041_);
                            v___x_2042_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_expr_2041_,
                                v_a_1806_,
                            );
                            v_fst_2043_ = leanh::lean_ctor_get(v___x_2042_, 0);
                            v_snd_2044_ = leanh::lean_ctor_get(v___x_2042_, 1);
                            v_isSharedCheck_2058_ =
                                (!leanh::lean_is_exclusive(v___x_2042_)) as u8;
                            if v_isSharedCheck_2058_ == 0 {
                                v___x_2046_ = v___x_2042_;
                                v_isShared_2047_ = v_isSharedCheck_2058_;
                                state = 31;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_2044_);
                                leanh::lean_inc(v_fst_2043_);
                                leanh::lean_dec(v___x_2042_);
                                v___x_2046_ = leanh::lean_box(0);
                                v_isShared_2047_ = v_isSharedCheck_2058_;
                                state = 31;
                                continue;
                            }
                        }
                        11 => {
                            v_typeName_2059_ = leanh::lean_ctor_get(v_e_1805_, 0);
                            v_idx_2060_ = leanh::lean_ctor_get(v_e_1805_, 1);
                            v_struct_2061_ = leanh::lean_ctor_get(v_e_1805_, 2);
                            leanh::lean_inc_ref(v_struct_2061_);
                            v___x_2062_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(
                                v_struct_2061_,
                                v_a_1806_,
                            );
                            v_fst_2063_ = leanh::lean_ctor_get(v___x_2062_, 0);
                            v_snd_2064_ = leanh::lean_ctor_get(v___x_2062_, 1);
                            v_isSharedCheck_2078_ =
                                (!leanh::lean_is_exclusive(v___x_2062_)) as u8;
                            if v_isSharedCheck_2078_ == 0 {
                                v___x_2066_ = v___x_2062_;
                                v_isShared_2067_ = v_isSharedCheck_2078_;
                                state = 34;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_2064_);
                                leanh::lean_inc(v_fst_2063_);
                                leanh::lean_dec(v___x_2062_);
                                v___x_2066_ = leanh::lean_box(0);
                                v_isShared_2067_ = v_isSharedCheck_2078_;
                                state = 34;
                                continue;
                            }
                        }
                        _ => {
                            v___x_2079_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2079_, 0, v_e_1805_);
                            leanh::lean_ctor_set(v___x_2079_, 1, v_a_1806_);
                            return v___x_2079_;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_fst_1827_);
                v___x_1832_ = l_Lean_mkFVar(v_fst_1827_);
                v___x_1861_ = l_Lean_Name_isAnonymous(v_userName_1813_);
                if v___x_1861_ == 0 {
                    v_userName_1834_ = v_userName_1813_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_userName_1813_);
                    v_fvars_1862_ = leanh::lean_ctor_get(v_snd_1828_, 5);
                    v___x_1863_ = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1;
                    v___x_1864_ = lean_array_get_size(v_fvars_1862_);
                    v___x_1865_ = lean_name_append_index_after(v___x_1863_, v___x_1864_);
                    v_userName_1834_ = v___x_1865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_ngen_1835_ = leanh::lean_ctor_get(v_snd_1828_, 0);
                v_lctx_1836_ = leanh::lean_ctor_get(v_snd_1828_, 1);
                v_mctx_1837_ = leanh::lean_ctor_get(v_snd_1828_, 2);
                v_nextParamIdx_1838_ = leanh::lean_ctor_get(v_snd_1828_, 3);
                v_paramNames_1839_ = leanh::lean_ctor_get(v_snd_1828_, 4);
                v_fvars_1840_ = leanh::lean_ctor_get(v_snd_1828_, 5);
                v_mvars_1841_ = leanh::lean_ctor_get(v_snd_1828_, 6);
                v_lmap_1842_ = leanh::lean_ctor_get(v_snd_1828_, 7);
                v_emap_1843_ = leanh::lean_ctor_get(v_snd_1828_, 8);
                v_abstractLevels_1844_ = leanh::lean_ctor_get_uint8(
                    v_snd_1828_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                );
                v_isSharedCheck_1860_ = (!leanh::lean_is_exclusive(v_snd_1828_)) as u8;
                if v_isSharedCheck_1860_ == 0 {
                    v___x_1846_ = v_snd_1828_;
                    v_isShared_1847_ = v_isSharedCheck_1860_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_emap_1843_);
                    leanh::lean_inc(v_lmap_1842_);
                    leanh::lean_inc(v_mvars_1841_);
                    leanh::lean_inc(v_fvars_1840_);
                    leanh::lean_inc(v_paramNames_1839_);
                    leanh::lean_inc(v_nextParamIdx_1838_);
                    leanh::lean_inc(v_mctx_1837_);
                    leanh::lean_inc(v_lctx_1836_);
                    leanh::lean_inc(v_ngen_1835_);
                    leanh::lean_dec(v_snd_1828_);
                    v___x_1846_ = leanh::lean_box(0);
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
                leanh::lean_inc_ref_n(v___x_1832_, 2);
                v___x_1851_ = lean_array_push(v_fvars_1840_, v___x_1832_);
                v___x_1852_ = lean_array_push(v_mvars_1841_, v_e_1805_);
                v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_emap_1843_, v_mvarId_1809_, v___x_1832_);
                if v_isShared_1847_ == 0 {
                    leanh::lean_ctor_set(v___x_1846_, 8, v___x_1853_);
                    leanh::lean_ctor_set(v___x_1846_, 6, v___x_1852_);
                    leanh::lean_ctor_set(v___x_1846_, 5, v___x_1851_);
                    leanh::lean_ctor_set(v___x_1846_, 1, v___x_1850_);
                    v___x_1855_ = v___x_1846_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1859_ = leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_ngen_1835_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___x_1850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_mctx_1837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_nextParamIdx_1838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_paramNames_1839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 5, v___x_1851_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 6, v___x_1852_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 7, v_lmap_1842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 8, v___x_1853_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1859_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                        v_abstractLevels_1844_,
                    );
                    v___x_1855_ = v_reuseFailAlloc_1859_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1831_ == 0 {
                    leanh::lean_ctor_set(v___x_1830_, 1, v___x_1855_);
                    leanh::lean_ctor_set(v___x_1830_, 0, v___x_1832_);
                    v___x_1857_ = v___x_1830_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1832_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1855_);
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
                    leanh::lean_dec_ref_known(v_e_1805_, 1);
                    v___x_1879_ = l_Lean_Expr_sort___override(v_fst_1871_);
                    if v_isShared_1875_ == 0 {
                        leanh::lean_ctor_set(v___x_1874_, 0, v___x_1879_);
                        v___x_1881_ = v___x_1874_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1882_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_snd_1872_);
                        v___x_1881_ = v_reuseFailAlloc_1882_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1871_);
                    if v_isShared_1875_ == 0 {
                        leanh::lean_ctor_set(v___x_1874_, 0, v_e_1805_);
                        v___x_1884_ = v___x_1874_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1885_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_e_1805_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_snd_1872_);
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
                    leanh::lean_inc(v_declName_1887_);
                    leanh::lean_dec_ref_known(v_e_1805_, 2);
                    v___x_1897_ = l_Lean_Expr_const___override(v_declName_1887_, v_fst_1891_);
                    if v_isShared_1895_ == 0 {
                        leanh::lean_ctor_set(v___x_1894_, 0, v___x_1897_);
                        v___x_1899_ = v___x_1894_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1900_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_snd_1892_);
                        v___x_1899_ = v_reuseFailAlloc_1900_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1891_);
                    if v_isShared_1895_ == 0 {
                        leanh::lean_ctor_set(v___x_1894_, 0, v_e_1805_);
                        v___x_1902_ = v___x_1894_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1903_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_e_1805_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_snd_1892_);
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
                    leanh::lean_dec_ref_known(v_e_1805_, 2);
                    v___x_1918_ = l_Lean_Expr_app___override(v_fst_1908_, v_fst_1911_);
                    if v_isShared_1915_ == 0 {
                        leanh::lean_ctor_set(v___x_1914_, 0, v___x_1918_);
                        v___x_1920_ = v___x_1914_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1921_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_snd_1912_);
                        v___x_1920_ = v_reuseFailAlloc_1921_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1911_);
                    leanh::lean_dec(v_fst_1908_);
                    if v_isShared_1915_ == 0 {
                        leanh::lean_ctor_set(v___x_1914_, 0, v_e_1805_);
                        v___x_1923_ = v___x_1914_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1924_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_e_1805_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_snd_1912_);
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
                    leanh::lean_inc(v_binderName_1932_);
                    leanh::lean_dec_ref_known(v_e_1805_, 3);
                    v___x_1947_ = l_Lean_Expr_lam___override(
                        v_binderName_1932_,
                        v_fst_1937_,
                        v_fst_1940_,
                        v_binderInfo_1935_,
                    );
                    if v_isShared_1944_ == 0 {
                        leanh::lean_ctor_set(v___x_1943_, 0, v___x_1947_);
                        v___x_1949_ = v___x_1943_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1950_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_snd_1941_);
                        v___x_1949_ = v_reuseFailAlloc_1950_;
                        state = 18;
                        continue;
                    }
                } else {
                    v___x_1951_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1935_, v_binderInfo_1935_);
                    if v___x_1951_ == 0 {
                        leanh::lean_inc(v_binderName_1932_);
                        leanh::lean_dec_ref_known(v_e_1805_, 3);
                        v___x_1952_ = l_Lean_Expr_lam___override(
                            v_binderName_1932_,
                            v_fst_1937_,
                            v_fst_1940_,
                            v_binderInfo_1935_,
                        );
                        if v_isShared_1944_ == 0 {
                            leanh::lean_ctor_set(v___x_1943_, 0, v___x_1952_);
                            v___x_1954_ = v___x_1943_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1955_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_snd_1941_);
                            v___x_1954_ = v_reuseFailAlloc_1955_;
                            state = 19;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_1940_);
                        leanh::lean_dec(v_fst_1937_);
                        if v_isShared_1944_ == 0 {
                            leanh::lean_ctor_set(v___x_1943_, 0, v_e_1805_);
                            v___x_1957_ = v___x_1943_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_1958_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_e_1805_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_snd_1941_);
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
                    leanh::lean_inc(v_binderName_1966_);
                    leanh::lean_dec_ref_known(v_e_1805_, 3);
                    v___x_1981_ = l_Lean_Expr_forallE___override(
                        v_binderName_1966_,
                        v_fst_1971_,
                        v_fst_1974_,
                        v_binderInfo_1969_,
                    );
                    if v_isShared_1978_ == 0 {
                        leanh::lean_ctor_set(v___x_1977_, 0, v___x_1981_);
                        v___x_1983_ = v___x_1977_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_snd_1975_);
                        v___x_1983_ = v_reuseFailAlloc_1984_;
                        state = 23;
                        continue;
                    }
                } else {
                    v___x_1985_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1969_, v_binderInfo_1969_);
                    if v___x_1985_ == 0 {
                        leanh::lean_inc(v_binderName_1966_);
                        leanh::lean_dec_ref_known(v_e_1805_, 3);
                        v___x_1986_ = l_Lean_Expr_forallE___override(
                            v_binderName_1966_,
                            v_fst_1971_,
                            v_fst_1974_,
                            v_binderInfo_1969_,
                        );
                        if v_isShared_1978_ == 0 {
                            leanh::lean_ctor_set(v___x_1977_, 0, v___x_1986_);
                            v___x_1988_ = v___x_1977_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_1989_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_snd_1975_);
                            v___x_1988_ = v_reuseFailAlloc_1989_;
                            state = 24;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_1974_);
                        leanh::lean_dec(v_fst_1971_);
                        if v_isShared_1978_ == 0 {
                            leanh::lean_ctor_set(v___x_1977_, 0, v_e_1805_);
                            v___x_1991_ = v___x_1977_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_1992_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_e_1805_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_snd_1975_);
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
                    leanh::lean_inc(v_declName_2000_);
                    leanh::lean_dec_ref_known(v_e_1805_, 4);
                    v___x_2019_ = l_Lean_Expr_letE___override(
                        v_declName_2000_,
                        v_fst_2006_,
                        v_fst_2009_,
                        v_fst_2012_,
                        v_nondep_2004_,
                    );
                    if v_isShared_2016_ == 0 {
                        leanh::lean_ctor_set(v___x_2015_, 0, v___x_2019_);
                        v___x_2021_ = v___x_2015_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_2022_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_snd_2013_);
                        v___x_2021_ = v_reuseFailAlloc_2022_;
                        state = 28;
                        continue;
                    }
                } else {
                    v___x_2023_ = lean_ptr_addr(v_body_2003_);
                    v___x_2024_ = lean_ptr_addr(v_fst_2012_);
                    v___x_2025_ = lean_usize_dec_eq(v___x_2023_, v___x_2024_);
                    if v___x_2025_ == 0 {
                        leanh::lean_inc(v_declName_2000_);
                        leanh::lean_dec_ref_known(v_e_1805_, 4);
                        v___x_2026_ = l_Lean_Expr_letE___override(
                            v_declName_2000_,
                            v_fst_2006_,
                            v_fst_2009_,
                            v_fst_2012_,
                            v_nondep_2004_,
                        );
                        if v_isShared_2016_ == 0 {
                            leanh::lean_ctor_set(v___x_2015_, 0, v___x_2026_);
                            v___x_2028_ = v___x_2015_;
                            state = 29;
                            continue;
                        } else {
                            v_reuseFailAlloc_2029_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_snd_2013_);
                            v___x_2028_ = v_reuseFailAlloc_2029_;
                            state = 29;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_2012_);
                        leanh::lean_dec(v_fst_2009_);
                        leanh::lean_dec(v_fst_2006_);
                        if v_isShared_2016_ == 0 {
                            leanh::lean_ctor_set(v___x_2015_, 0, v_e_1805_);
                            v___x_2031_ = v___x_2015_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_2032_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_e_1805_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_snd_2013_);
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
                    leanh::lean_inc(v_data_2040_);
                    leanh::lean_dec_ref_known(v_e_1805_, 2);
                    v___x_2051_ = l_Lean_Expr_mdata___override(v_data_2040_, v_fst_2043_);
                    if v_isShared_2047_ == 0 {
                        leanh::lean_ctor_set(v___x_2046_, 0, v___x_2051_);
                        v___x_2053_ = v___x_2046_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_2054_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_snd_2044_);
                        v___x_2053_ = v_reuseFailAlloc_2054_;
                        state = 32;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_2043_);
                    if v_isShared_2047_ == 0 {
                        leanh::lean_ctor_set(v___x_2046_, 0, v_e_1805_);
                        v___x_2056_ = v___x_2046_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_2057_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_e_1805_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2044_);
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
                    leanh::lean_inc(v_idx_2060_);
                    leanh::lean_inc(v_typeName_2059_);
                    leanh::lean_dec_ref_known(v_e_1805_, 3);
                    v___x_2071_ =
                        l_Lean_Expr_proj___override(v_typeName_2059_, v_idx_2060_, v_fst_2063_);
                    if v_isShared_2067_ == 0 {
                        leanh::lean_ctor_set(v___x_2066_, 0, v___x_2071_);
                        v___x_2073_ = v___x_2066_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_2074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_snd_2064_);
                        v___x_2073_ = v_reuseFailAlloc_2074_;
                        state = 35;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_2063_);
                    if v_isShared_2067_ == 0 {
                        leanh::lean_ctor_set(v___x_2066_, 0, v_e_1805_);
                        v___x_2076_ = v___x_2066_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_e_1805_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_snd_2064_);
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
    mut v_00_u03b2_2080_: *mut leanh::LeanObject,
    mut v_m_2081_: *mut leanh::LeanObject,
    mut v_a_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_2081_, v_a_2082_);
    return v___x_2083_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(
    mut v_00_u03b2_2084_: *mut leanh::LeanObject,
    mut v_m_2085_: *mut leanh::LeanObject,
    mut v_a_2086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(v_00_u03b2_2084_, v_m_2085_, v_a_2086_);
    leanh::lean_dec(v_a_2086_);
    leanh::lean_dec_ref(v_m_2085_);
    return v_res_2087_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(
    mut v_00_u03b2_2088_: *mut leanh::LeanObject,
    mut v_m_2089_: *mut leanh::LeanObject,
    mut v_a_2090_: *mut leanh::LeanObject,
    mut v_b_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_2089_, v_a_2090_, v_b_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(
    mut v_00_u03b2_2093_: *mut leanh::LeanObject,
    mut v_a_2094_: *mut leanh::LeanObject,
    mut v_x_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_2094_, v_x_2095_);
    return v___x_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_2097_: *mut leanh::LeanObject,
    mut v_a_2098_: *mut leanh::LeanObject,
    mut v_x_2099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(v_00_u03b2_2097_, v_a_2098_, v_x_2099_);
    leanh::lean_dec(v_x_2099_);
    leanh::lean_dec(v_a_2098_);
    return v_res_2100_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(
    mut v_00_u03b2_2101_: *mut leanh::LeanObject,
    mut v_a_2102_: *mut leanh::LeanObject,
    mut v_x_2103_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2104_: u8 = 0;
    v___x_2104_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_2102_, v_x_2103_);
    return v___x_2104_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(
    mut v_00_u03b2_2105_: *mut leanh::LeanObject,
    mut v_a_2106_: *mut leanh::LeanObject,
    mut v_x_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2108_: u8 = 0;
    let mut v_r_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(v_00_u03b2_2105_, v_a_2106_, v_x_2107_);
    leanh::lean_dec(v_x_2107_);
    leanh::lean_dec(v_a_2106_);
    v_r_2109_ = leanh::lean_box((v_res_2108_) as usize);
    return v_r_2109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4(
    mut v_00_u03b2_2110_: *mut leanh::LeanObject,
    mut v_data_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_data_2111_);
    return v___x_2112_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5(
    mut v_00_u03b2_2113_: *mut leanh::LeanObject,
    mut v_a_2114_: *mut leanh::LeanObject,
    mut v_b_2115_: *mut leanh::LeanObject,
    mut v_x_2116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_2114_, v_b_2115_, v_x_2116_);
    return v___x_2117_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2118_: *mut leanh::LeanObject,
    mut v_i_2119_: *mut leanh::LeanObject,
    mut v_source_2120_: *mut leanh::LeanObject,
    mut v_target_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v_i_2119_, v_source_2120_, v_target_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7(
    mut v_00_u03b2_2123_: *mut leanh::LeanObject,
    mut v_x_2124_: *mut leanh::LeanObject,
    mut v_x_2125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_x_2124_, v_x_2125_);
    return v___x_2126_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
    mut v_e_2127_: *mut leanh::LeanObject,
    mut v___y_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2130_: u8 = 0;
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_unused_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2130_ = l_Lean_Expr_hasMVar(v_e_2127_);
                if v___x_2130_ == 0 {
                    v___x_2131_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2131_, 0, v_e_2127_);
                    return v___x_2131_;
                } else {
                    v___x_2132_ = lean_st_ref_get(v___y_2128_);
                    v_mctx_2133_ = leanh::lean_ctor_get(v___x_2132_, 0);
                    leanh::lean_inc_ref(v_mctx_2133_);
                    leanh::lean_dec(v___x_2132_);
                    v___x_2134_ = l_Lean_instantiateMVarsCore(v_mctx_2133_, v_e_2127_);
                    v_fst_2135_ = leanh::lean_ctor_get(v___x_2134_, 0);
                    leanh::lean_inc(v_fst_2135_);
                    v_snd_2136_ = leanh::lean_ctor_get(v___x_2134_, 1);
                    leanh::lean_inc(v_snd_2136_);
                    leanh::lean_dec_ref(v___x_2134_);
                    v___x_2137_ = lean_st_ref_take(v___y_2128_);
                    v_cache_2138_ = leanh::lean_ctor_get(v___x_2137_, 1);
                    v_zetaDeltaFVarIds_2139_ = leanh::lean_ctor_get(v___x_2137_, 2);
                    v_postponed_2140_ = leanh::lean_ctor_get(v___x_2137_, 3);
                    v_diag_2141_ = leanh::lean_ctor_get(v___x_2137_, 4);
                    v_isSharedCheck_2150_ = (!leanh::lean_is_exclusive(v___x_2137_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v_unused_2151_ = leanh::lean_ctor_get(v___x_2137_, 0);
                        leanh::lean_dec(v_unused_2151_);
                        v___x_2143_ = v___x_2137_;
                        v_isShared_2144_ = v_isSharedCheck_2150_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_2141_);
                        leanh::lean_inc(v_postponed_2140_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_2139_);
                        leanh::lean_inc(v_cache_2138_);
                        leanh::lean_dec(v___x_2137_);
                        v___x_2143_ = leanh::lean_box(0);
                        v_isShared_2144_ = v_isSharedCheck_2150_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2144_ == 0 {
                    leanh::lean_ctor_set(v___x_2143_, 0, v_snd_2136_);
                    v___x_2146_ = v___x_2143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_snd_2136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_cache_2138_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2149_,
                        2,
                        v_zetaDeltaFVarIds_2139_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_postponed_2140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_diag_2141_);
                    v___x_2146_ = v_reuseFailAlloc_2149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2147_ = lean_st_ref_set(v___y_2128_, v___x_2146_);
                v___x_2148_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2148_, 0, v_fst_2135_);
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(
    mut v_e_2152_: *mut leanh::LeanObject,
    mut v___y_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2155_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
        v_e_2152_,
        v___y_2153_,
    );
    leanh::lean_dec(v___y_2153_);
    return v_res_2155_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(
    mut v_e_2156_: *mut leanh::LeanObject,
    mut v___y_2157_: *mut leanh::LeanObject,
    mut v___y_2158_: *mut leanh::LeanObject,
    mut v___y_2159_: *mut leanh::LeanObject,
    mut v___y_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2162_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
        v_e_2156_,
        v___y_2158_,
    );
    return v___x_2162_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(
    mut v_e_2163_: *mut leanh::LeanObject,
    mut v___y_2164_: *mut leanh::LeanObject,
    mut v___y_2165_: *mut leanh::LeanObject,
    mut v___y_2166_: *mut leanh::LeanObject,
    mut v___y_2167_: *mut leanh::LeanObject,
    mut v___y_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(
        v_e_2163_,
        v___y_2164_,
        v___y_2165_,
        v___y_2166_,
        v___y_2167_,
    );
    leanh::lean_dec(v___y_2167_);
    leanh::lean_dec_ref(v___y_2166_);
    leanh::lean_dec(v___y_2165_);
    leanh::lean_dec_ref(v___y_2164_);
    return v_res_2169_;
}
pub unsafe fn _init_l_Lean_Meta_abstractMVars___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = leanh::lean_box(0);
    v___x_2173_ = leanh::lean_unsigned_to_nat(16);
    v___x_2174_ = lean_mk_array(v___x_2173_, v___x_2172_);
    return v___x_2174_;
}
pub unsafe fn _init_l_Lean_Meta_abstractMVars___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2175_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__1_once),
        _init_l_Lean_Meta_abstractMVars___closed__1,
    );
    v___x_2176_ = leanh::lean_unsigned_to_nat(0);
    v___x_2177_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2177_, 0, v___x_2176_);
    leanh::lean_ctor_set(v___x_2177_, 1, v___x_2175_);
    return v___x_2177_;
}
pub unsafe fn l_Lean_Meta_abstractMVars(
    mut v_e_2178_: *mut leanh::LeanObject,
    mut v_levels_2179_: u8,
    mut v_a_2180_: *mut leanh::LeanObject,
    mut v_a_2181_: *mut leanh::LeanObject,
    mut v_a_2182_: *mut leanh::LeanObject,
    mut v_a_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvars_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_unused_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_unused_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2185_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(
                        v_e_2178_, v_a_2181_,
                    );
                v_a_2186_ = leanh::lean_ctor_get(v___x_2185_, 0);
                v_isSharedCheck_2247_ = (!leanh::lean_is_exclusive(v___x_2185_)) as u8;
                if v_isSharedCheck_2247_ == 0 {
                    v___x_2188_ = v___x_2185_;
                    v_isShared_2189_ = v_isSharedCheck_2247_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2186_);
                    leanh::lean_dec(v___x_2185_);
                    v___x_2188_ = leanh::lean_box(0);
                    v_isShared_2189_ = v_isSharedCheck_2247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2190_ = lean_st_ref_get(v_a_2181_);
                v___x_2191_ = lean_st_ref_get(v_a_2183_);
                v_mctx_2192_ = leanh::lean_ctor_get(v___x_2190_, 0);
                leanh::lean_inc_ref(v_mctx_2192_);
                leanh::lean_dec(v___x_2190_);
                v_lctx_2193_ = leanh::lean_ctor_get(v_a_2180_, 2);
                v_ngen_2194_ = leanh::lean_ctor_get(v___x_2191_, 2);
                leanh::lean_inc_ref(v_ngen_2194_);
                leanh::lean_dec(v___x_2191_);
                v___x_2195_ = leanh::lean_unsigned_to_nat(0);
                v___x_2196_ = l_Lean_Meta_abstractMVars___closed__0;
                v___x_2197_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_abstractMVars___closed__2_once),
                    _init_l_Lean_Meta_abstractMVars___closed__2,
                );
                leanh::lean_inc_ref(v_lctx_2193_);
                v___x_2198_ = leanh::lean_alloc_ctor(0, 9, (1) as u32);
                leanh::lean_ctor_set(v___x_2198_, 0, v_ngen_2194_);
                leanh::lean_ctor_set(v___x_2198_, 1, v_lctx_2193_);
                leanh::lean_ctor_set(v___x_2198_, 2, v_mctx_2192_);
                leanh::lean_ctor_set(v___x_2198_, 3, v___x_2195_);
                leanh::lean_ctor_set(v___x_2198_, 4, v___x_2196_);
                leanh::lean_ctor_set(v___x_2198_, 5, v___x_2196_);
                leanh::lean_ctor_set(v___x_2198_, 6, v___x_2196_);
                leanh::lean_ctor_set(v___x_2198_, 7, v___x_2197_);
                leanh::lean_ctor_set(v___x_2198_, 8, v___x_2197_);
                leanh::lean_ctor_set_uint8(
                    v___x_2198_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                    v_levels_2179_,
                );
                v___x_2199_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_a_2186_, v___x_2198_);
                v_fst_2200_ = leanh::lean_ctor_get(v___x_2199_, 0);
                leanh::lean_inc(v_fst_2200_);
                v_snd_2201_ = leanh::lean_ctor_get(v___x_2199_, 1);
                leanh::lean_inc(v_snd_2201_);
                leanh::lean_dec_ref(v___x_2199_);
                v___x_2202_ = lean_st_ref_take(v_a_2183_);
                v_ngen_2203_ = leanh::lean_ctor_get(v_snd_2201_, 0);
                leanh::lean_inc_ref(v_ngen_2203_);
                v_lctx_2204_ = leanh::lean_ctor_get(v_snd_2201_, 1);
                leanh::lean_inc_ref(v_lctx_2204_);
                v_mctx_2205_ = leanh::lean_ctor_get(v_snd_2201_, 2);
                leanh::lean_inc_ref(v_mctx_2205_);
                v_paramNames_2206_ = leanh::lean_ctor_get(v_snd_2201_, 4);
                leanh::lean_inc_ref(v_paramNames_2206_);
                v_fvars_2207_ = leanh::lean_ctor_get(v_snd_2201_, 5);
                leanh::lean_inc_ref(v_fvars_2207_);
                v_mvars_2208_ = leanh::lean_ctor_get(v_snd_2201_, 6);
                leanh::lean_inc_ref(v_mvars_2208_);
                leanh::lean_dec(v_snd_2201_);
                v_env_2209_ = leanh::lean_ctor_get(v___x_2202_, 0);
                v_nextMacroScope_2210_ = leanh::lean_ctor_get(v___x_2202_, 1);
                v_auxDeclNGen_2211_ = leanh::lean_ctor_get(v___x_2202_, 3);
                v_traceState_2212_ = leanh::lean_ctor_get(v___x_2202_, 4);
                v_cache_2213_ = leanh::lean_ctor_get(v___x_2202_, 5);
                v_messages_2214_ = leanh::lean_ctor_get(v___x_2202_, 6);
                v_infoState_2215_ = leanh::lean_ctor_get(v___x_2202_, 7);
                v_snapshotTasks_2216_ = leanh::lean_ctor_get(v___x_2202_, 8);
                v_isSharedCheck_2245_ = (!leanh::lean_is_exclusive(v___x_2202_)) as u8;
                if v_isSharedCheck_2245_ == 0 {
                    v_unused_2246_ = leanh::lean_ctor_get(v___x_2202_, 2);
                    leanh::lean_dec(v_unused_2246_);
                    v___x_2218_ = v___x_2202_;
                    v_isShared_2219_ = v_isSharedCheck_2245_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2216_);
                    leanh::lean_inc(v_infoState_2215_);
                    leanh::lean_inc(v_messages_2214_);
                    leanh::lean_inc(v_cache_2213_);
                    leanh::lean_inc(v_traceState_2212_);
                    leanh::lean_inc(v_auxDeclNGen_2211_);
                    leanh::lean_inc(v_nextMacroScope_2210_);
                    leanh::lean_inc(v_env_2209_);
                    leanh::lean_dec(v___x_2202_);
                    v___x_2218_ = leanh::lean_box(0);
                    v_isShared_2219_ = v_isSharedCheck_2245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2219_ == 0 {
                    leanh::lean_ctor_set(v___x_2218_, 2, v_ngen_2203_);
                    v___x_2221_ = v___x_2218_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2244_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_env_2209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_nextMacroScope_2210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_ngen_2203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_auxDeclNGen_2211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_traceState_2212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 5, v_cache_2213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 6, v_messages_2214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 7, v_infoState_2215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 8, v_snapshotTasks_2216_);
                    v___x_2221_ = v_reuseFailAlloc_2244_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2222_ = lean_st_ref_set(v_a_2183_, v___x_2221_);
                v___x_2223_ = lean_st_ref_take(v_a_2181_);
                v_cache_2224_ = leanh::lean_ctor_get(v___x_2223_, 1);
                v_zetaDeltaFVarIds_2225_ = leanh::lean_ctor_get(v___x_2223_, 2);
                v_postponed_2226_ = leanh::lean_ctor_get(v___x_2223_, 3);
                v_diag_2227_ = leanh::lean_ctor_get(v___x_2223_, 4);
                v_isSharedCheck_2242_ = (!leanh::lean_is_exclusive(v___x_2223_)) as u8;
                if v_isSharedCheck_2242_ == 0 {
                    v_unused_2243_ = leanh::lean_ctor_get(v___x_2223_, 0);
                    leanh::lean_dec(v_unused_2243_);
                    v___x_2229_ = v___x_2223_;
                    v_isShared_2230_ = v_isSharedCheck_2242_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2227_);
                    leanh::lean_inc(v_postponed_2226_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2225_);
                    leanh::lean_inc(v_cache_2224_);
                    leanh::lean_dec(v___x_2223_);
                    v___x_2229_ = leanh::lean_box(0);
                    v_isShared_2230_ = v_isSharedCheck_2242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2230_ == 0 {
                    leanh::lean_ctor_set(v___x_2229_, 0, v_mctx_2205_);
                    v___x_2232_ = v___x_2229_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_mctx_2205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_cache_2224_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2241_,
                        2,
                        v_zetaDeltaFVarIds_2225_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_postponed_2226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_diag_2227_);
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
                leanh::lean_dec(v_fst_2200_);
                leanh::lean_dec_ref(v_fvars_2207_);
                v___x_2237_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2237_, 0, v_paramNames_2206_);
                leanh::lean_ctor_set(v___x_2237_, 1, v_mvars_2208_);
                leanh::lean_ctor_set(v___x_2237_, 2, v___x_2236_);
                if v_isShared_2189_ == 0 {
                    leanh::lean_ctor_set(v___x_2188_, 0, v___x_2237_);
                    v___x_2239_ = v___x_2188_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
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
    mut v_e_2248_: *mut leanh::LeanObject,
    mut v_levels_2249_: *mut leanh::LeanObject,
    mut v_a_2250_: *mut leanh::LeanObject,
    mut v_a_2251_: *mut leanh::LeanObject,
    mut v_a_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
    mut v_a_2254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_levels_boxed_2255_: u8 = 0;
    let mut v_res_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_levels_boxed_2255_ = (leanh::lean_unbox(v_levels_2249_) as u8);
    v_res_2256_ = l_Lean_Meta_abstractMVars(
        v_e_2248_,
        v_levels_boxed_2255_,
        v_a_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
    );
    leanh::lean_dec(v_a_2253_);
    leanh::lean_dec_ref(v_a_2252_);
    leanh::lean_dec(v_a_2251_);
    leanh::lean_dec_ref(v_a_2250_);
    return v_res_2256_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(
    mut v_sz_2257_: usize,
    mut v_i_2258_: usize,
    mut v_bs_2259_: *mut leanh::LeanObject,
    mut v___y_2260_: *mut leanh::LeanObject,
    mut v___y_2261_: *mut leanh::LeanObject,
    mut v___y_2262_: *mut leanh::LeanObject,
    mut v___y_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: usize = 0;
    let mut v___x_2272_: usize = 0;
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2265_ = lean_usize_dec_lt(v_i_2258_, v_sz_2257_);
                if v___x_2265_ == 0 {
                    v___x_2266_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2266_, 0, v_bs_2259_);
                    return v___x_2266_;
                } else {
                    v___x_2267_ = l_Lean_Meta_mkFreshLevelMVar(
                        v___y_2260_,
                        v___y_2261_,
                        v___y_2262_,
                        v___y_2263_,
                    );
                    if leanh::lean_obj_tag(v___x_2267_) == 0 {
                        v_a_2268_ = leanh::lean_ctor_get(v___x_2267_, 0);
                        leanh::lean_inc(v_a_2268_);
                        leanh::lean_dec_ref_known(v___x_2267_, 1);
                        v___x_2269_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2270_ = lean_array_uset(v_bs_2259_, v_i_2258_, v___x_2269_);
                        v___x_2271_ = 1usize;
                        v___x_2272_ = lean_usize_add(v_i_2258_, v___x_2271_);
                        v___x_2273_ = lean_array_uset(v_bs_x27_2270_, v_i_2258_, v_a_2268_);
                        v_i_2258_ = v___x_2272_;
                        v_bs_2259_ = v___x_2273_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_2259_);
                        v_a_2275_ = leanh::lean_ctor_get(v___x_2267_, 0);
                        v_isSharedCheck_2282_ =
                            (!leanh::lean_is_exclusive(v___x_2267_)) as u8;
                        if v_isSharedCheck_2282_ == 0 {
                            v___x_2277_ = v___x_2267_;
                            v_isShared_2278_ = v_isSharedCheck_2282_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2275_);
                            leanh::lean_dec(v___x_2267_);
                            v___x_2277_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2281_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
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
    mut v_sz_2283_: *mut leanh::LeanObject,
    mut v_i_2284_: *mut leanh::LeanObject,
    mut v_bs_2285_: *mut leanh::LeanObject,
    mut v___y_2286_: *mut leanh::LeanObject,
    mut v___y_2287_: *mut leanh::LeanObject,
    mut v___y_2288_: *mut leanh::LeanObject,
    mut v___y_2289_: *mut leanh::LeanObject,
    mut v___y_2290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2291_: usize = 0;
    let mut v_i_boxed_2292_: usize = 0;
    let mut v_res_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2291_ = leanh::lean_unbox_usize(v_sz_2283_);
    leanh::lean_dec(v_sz_2283_);
    v_i_boxed_2292_ = leanh::lean_unbox_usize(v_i_2284_);
    leanh::lean_dec(v_i_2284_);
    v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_boxed_2291_, v_i_boxed_2292_, v_bs_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
    leanh::lean_dec(v___y_2289_);
    leanh::lean_dec_ref(v___y_2288_);
    leanh::lean_dec(v___y_2287_);
    leanh::lean_dec_ref(v___y_2286_);
    return v_res_2293_;
}
pub unsafe fn l_Lean_Meta_openAbstractMVarsResult(
    mut v_a_2294_: *mut leanh::LeanObject,
    mut v_a_2295_: *mut leanh::LeanObject,
    mut v_a_2296_: *mut leanh::LeanObject,
    mut v_a_2297_: *mut leanh::LeanObject,
    mut v_a_2298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_paramNames_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2302_: usize = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_paramNames_2300_ = leanh::lean_ctor_get(v_a_2294_, 0);
                v_expr_2301_ = leanh::lean_ctor_get(v_a_2294_, 2);
                v_sz_2302_ = lean_array_size(v_paramNames_2300_);
                v___x_2303_ = 0usize;
                leanh::lean_inc_ref(v_paramNames_2300_);
                v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_2302_, v___x_2303_, v_paramNames_2300_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
                if leanh::lean_obj_tag(v___x_2304_) == 0 {
                    v_a_2305_ = leanh::lean_ctor_get(v___x_2304_, 0);
                    leanh::lean_inc(v_a_2305_);
                    leanh::lean_dec_ref_known(v___x_2304_, 1);
                    leanh::lean_inc_ref(v_paramNames_2300_);
                    v___x_2306_ = l_Lean_Expr_instantiateLevelParamsArray(
                        v_expr_2301_,
                        v_paramNames_2300_,
                        v_a_2305_,
                    );
                    v___x_2307_ = l_Lean_Meta_AbstractMVarsResult_numMVars(v_a_2294_);
                    leanh::lean_dec_ref(v_a_2294_);
                    v___x_2308_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
                    v___x_2309_ = l_Lean_Meta_lambdaMetaTelescope(
                        v___x_2306_,
                        v___x_2308_,
                        v_a_2295_,
                        v_a_2296_,
                        v_a_2297_,
                        v_a_2298_,
                    );
                    leanh::lean_dec_ref_known(v___x_2308_, 1);
                    leanh::lean_dec_ref(v___x_2306_);
                    return v___x_2309_;
                } else {
                    leanh::lean_dec_ref(v_a_2294_);
                    v_a_2310_ = leanh::lean_ctor_get(v___x_2304_, 0);
                    v_isSharedCheck_2317_ = (!leanh::lean_is_exclusive(v___x_2304_)) as u8;
                    if v_isSharedCheck_2317_ == 0 {
                        v___x_2312_ = v___x_2304_;
                        v_isShared_2313_ = v_isSharedCheck_2317_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2310_);
                        leanh::lean_dec(v___x_2304_);
                        v___x_2312_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2316_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
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
    mut v_a_2318_: *mut leanh::LeanObject,
    mut v_a_2319_: *mut leanh::LeanObject,
    mut v_a_2320_: *mut leanh::LeanObject,
    mut v_a_2321_: *mut leanh::LeanObject,
    mut v_a_2322_: *mut leanh::LeanObject,
    mut v_a_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2324_ =
        l_Lean_Meta_openAbstractMVarsResult(v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
    leanh::lean_dec(v_a_2322_);
    leanh::lean_dec_ref(v_a_2321_);
    leanh::lean_dec(v_a_2320_);
    leanh::lean_dec_ref(v_a_2319_);
    return v_res_2324_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_AbstractMVars(
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
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_AbstractMVars(
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
pub unsafe fn initialize_Lean_Meta_AbstractMVars(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Lean_Meta_AbstractMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_AbstractMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_AbstractMVars(builtin);
}