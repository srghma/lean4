// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.Util
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.InferType Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.LitValues
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_whnfD;
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProofQuick, l_Lean_Meta_isPropQuick};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::InferType::{
    initialize_Lean_Meta_Sym_InferType, l_Lean_Meta_Sym_inferType___redArg,
    runtime_initialize_Lean_Meta_Sym_InferType,
};
use crate::r#gen::Lean::Meta::Sym::LitValues::{
    initialize_Lean_Meta_Sym_LitValues, l_Lean_Meta_Sym_getBitVecValue_x3f,
    l_Lean_Meta_Sym_getCharValue_x3f, l_Lean_Meta_Sym_getFinValue_x3f,
    l_Lean_Meta_Sym_getInt8Value_x3f, l_Lean_Meta_Sym_getInt16Value_x3f,
    l_Lean_Meta_Sym_getInt32Value_x3f, l_Lean_Meta_Sym_getInt64Value_x3f,
    l_Lean_Meta_Sym_getIntValue_x3f, l_Lean_Meta_Sym_getNatValue_x3f,
    l_Lean_Meta_Sym_getRatValue_x3f, l_Lean_Meta_Sym_getStringValue_x3f,
    l_Lean_Meta_Sym_getUInt8Value_x3f, l_Lean_Meta_Sym_getUInt16Value_x3f,
    l_Lean_Meta_Sym_getUInt32Value_x3f, l_Lean_Meta_Sym_getUInt64Value_x3f,
    runtime_initialize_Lean_Meta_Sym_LitValues,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::lean_imports_rs::Init::Prelude::lean_array_push;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::MetavarContext::lean_instantiate_level_mvars;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__13_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__13_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__16_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__17_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__18_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__19_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__20_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__21_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__22_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__23_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__24_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__25_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__26_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__25_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_isVal___closed__27_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_isVal___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_isVal___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0_value:
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
    m_data: [76, 105, 115, 116, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 105, 108, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9582258842178272501 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18135193680607614554 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__3_value:
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
    m_data: [99, 111, 110, 115, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9582258842178272501 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8614124190858717794 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(
    mut v_e_641_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_642_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_641_);
    if crate::leanh::lean_obj_tag(v___x_642_) == 0 {
        let mut v___x_643_: u8 = 0;
        v___x_643_ = 0;
        return v___x_643_;
    } else {
        let mut v___x_644_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_642_, 1);
        v___x_644_ = 1;
        return v___x_644_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue___boxed(
    mut v_e_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_646_: u8 = 0;
    let mut v_r_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_646_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(v_e_645_);
    v_r_647_ = crate::leanh::lean_box((v_res_646_) as usize);
    return v_r_647_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(
    mut v_e_648_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_649_ = l_Lean_Meta_Sym_getStringValue_x3f(v_e_648_);
    if crate::leanh::lean_obj_tag(v___x_649_) == 0 {
        let mut v___x_650_: u8 = 0;
        v___x_650_ = 0;
        return v___x_650_;
    } else {
        let mut v___x_651_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_649_, 1);
        v___x_651_ = 1;
        return v___x_651_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue___boxed(
    mut v_e_652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_653_: u8 = 0;
    let mut v_r_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_653_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(v_e_652_);
    v_r_654_ = crate::leanh::lean_box((v_res_653_) as usize);
    return v_r_654_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(
    mut v_e_655_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_655_);
    if crate::leanh::lean_obj_tag(v___x_656_) == 0 {
        let mut v___x_657_: u8 = 0;
        v___x_657_ = 0;
        return v___x_657_;
    } else {
        let mut v___x_658_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_656_, 1);
        v___x_658_ = 1;
        return v___x_658_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue___boxed(
    mut v_e_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_660_: u8 = 0;
    let mut v_r_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(v_e_659_);
    v_r_661_ = crate::leanh::lean_box((v_res_660_) as usize);
    return v_r_661_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(
    mut v_e_662_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_663_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_e_662_);
    if crate::leanh::lean_obj_tag(v___x_663_) == 0 {
        let mut v___x_664_: u8 = 0;
        v___x_664_ = 0;
        return v___x_664_;
    } else {
        let mut v___x_665_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_663_, 1);
        v___x_665_ = 1;
        return v___x_665_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue___boxed(
    mut v_e_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_667_: u8 = 0;
    let mut v_r_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_667_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(v_e_666_);
    v_r_668_ = crate::leanh::lean_box((v_res_667_) as usize);
    return v_r_668_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(
    mut v_e_669_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = l_Lean_Meta_Sym_getFinValue_x3f(v_e_669_);
    if crate::leanh::lean_obj_tag(v___x_670_) == 0 {
        let mut v___x_671_: u8 = 0;
        v___x_671_ = 0;
        return v___x_671_;
    } else {
        let mut v___x_672_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_670_, 1);
        v___x_672_ = 1;
        return v___x_672_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue___boxed(
    mut v_e_673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_674_: u8 = 0;
    let mut v_r_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(v_e_673_);
    v_r_675_ = crate::leanh::lean_box((v_res_674_) as usize);
    return v_r_675_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(
    mut v_e_676_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_677_ = l_Lean_Meta_Sym_getCharValue_x3f(v_e_676_);
    if crate::leanh::lean_obj_tag(v___x_677_) == 0 {
        let mut v___x_678_: u8 = 0;
        v___x_678_ = 0;
        return v___x_678_;
    } else {
        let mut v___x_679_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_677_, 1);
        v___x_679_ = 1;
        return v___x_679_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue___boxed(
    mut v_e_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_681_: u8 = 0;
    let mut v_r_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_681_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(v_e_680_);
    v_r_682_ = crate::leanh::lean_box((v_res_681_) as usize);
    return v_r_682_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(
    mut v_e_683_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = l_Lean_Meta_Sym_getRatValue_x3f(v_e_683_);
    if crate::leanh::lean_obj_tag(v___x_684_) == 0 {
        let mut v___x_685_: u8 = 0;
        v___x_685_ = 0;
        return v___x_685_;
    } else {
        let mut v___x_686_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_684_, 1);
        v___x_686_ = 1;
        return v___x_686_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue___boxed(
    mut v_e_687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_688_: u8 = 0;
    let mut v_r_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_688_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(v_e_687_);
    v_r_689_ = crate::leanh::lean_box((v_res_688_) as usize);
    return v_r_689_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(
    mut v_e_690_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v_e_690_);
    if crate::leanh::lean_obj_tag(v___x_691_) == 0 {
        let mut v___x_692_: u8 = 0;
        v___x_692_ = 0;
        return v___x_692_;
    } else {
        let mut v___x_693_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_691_, 1);
        v___x_693_ = 1;
        return v___x_693_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value___boxed(
    mut v_e_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_695_: u8 = 0;
    let mut v_r_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_695_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(v_e_694_);
    v_r_696_ = crate::leanh::lean_box((v_res_695_) as usize);
    return v_r_696_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(
    mut v_e_697_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v_e_697_);
    if crate::leanh::lean_obj_tag(v___x_698_) == 0 {
        let mut v___x_699_: u8 = 0;
        v___x_699_ = 0;
        return v___x_699_;
    } else {
        let mut v___x_700_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_698_, 1);
        v___x_700_ = 1;
        return v___x_700_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value___boxed(
    mut v_e_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_702_: u8 = 0;
    let mut v_r_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_702_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(v_e_701_);
    v_r_703_ = crate::leanh::lean_box((v_res_702_) as usize);
    return v_r_703_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(
    mut v_e_704_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_705_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v_e_704_);
    if crate::leanh::lean_obj_tag(v___x_705_) == 0 {
        let mut v___x_706_: u8 = 0;
        v___x_706_ = 0;
        return v___x_706_;
    } else {
        let mut v___x_707_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_705_, 1);
        v___x_707_ = 1;
        return v___x_707_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value___boxed(
    mut v_e_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_709_: u8 = 0;
    let mut v_r_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_709_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(v_e_708_);
    v_r_710_ = crate::leanh::lean_box((v_res_709_) as usize);
    return v_r_710_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(
    mut v_e_711_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v_e_711_);
    if crate::leanh::lean_obj_tag(v___x_712_) == 0 {
        let mut v___x_713_: u8 = 0;
        v___x_713_ = 0;
        return v___x_713_;
    } else {
        let mut v___x_714_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_712_, 1);
        v___x_714_ = 1;
        return v___x_714_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value___boxed(
    mut v_e_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_716_: u8 = 0;
    let mut v_r_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_716_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(v_e_715_);
    v_r_717_ = crate::leanh::lean_box((v_res_716_) as usize);
    return v_r_717_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(
    mut v_e_718_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = l_Lean_Meta_Sym_getInt8Value_x3f(v_e_718_);
    if crate::leanh::lean_obj_tag(v___x_719_) == 0 {
        let mut v___x_720_: u8 = 0;
        v___x_720_ = 0;
        return v___x_720_;
    } else {
        let mut v___x_721_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_719_, 1);
        v___x_721_ = 1;
        return v___x_721_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value___boxed(
    mut v_e_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_723_: u8 = 0;
    let mut v_r_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(v_e_722_);
    v_r_724_ = crate::leanh::lean_box((v_res_723_) as usize);
    return v_r_724_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(
    mut v_e_725_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_726_ = l_Lean_Meta_Sym_getInt16Value_x3f(v_e_725_);
    if crate::leanh::lean_obj_tag(v___x_726_) == 0 {
        let mut v___x_727_: u8 = 0;
        v___x_727_ = 0;
        return v___x_727_;
    } else {
        let mut v___x_728_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_726_, 1);
        v___x_728_ = 1;
        return v___x_728_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value___boxed(
    mut v_e_729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_730_: u8 = 0;
    let mut v_r_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_730_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(v_e_729_);
    v_r_731_ = crate::leanh::lean_box((v_res_730_) as usize);
    return v_r_731_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(
    mut v_e_732_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = l_Lean_Meta_Sym_getInt32Value_x3f(v_e_732_);
    if crate::leanh::lean_obj_tag(v___x_733_) == 0 {
        let mut v___x_734_: u8 = 0;
        v___x_734_ = 0;
        return v___x_734_;
    } else {
        let mut v___x_735_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_733_, 1);
        v___x_735_ = 1;
        return v___x_735_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value___boxed(
    mut v_e_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_737_: u8 = 0;
    let mut v_r_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_737_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(v_e_736_);
    v_r_738_ = crate::leanh::lean_box((v_res_737_) as usize);
    return v_r_738_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(
    mut v_e_739_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ = l_Lean_Meta_Sym_getInt64Value_x3f(v_e_739_);
    if crate::leanh::lean_obj_tag(v___x_740_) == 0 {
        let mut v___x_741_: u8 = 0;
        v___x_741_ = 0;
        return v___x_741_;
    } else {
        let mut v___x_742_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_740_, 1);
        v___x_742_ = 1;
        return v___x_742_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value___boxed(
    mut v_e_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_744_: u8 = 0;
    let mut v_r_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_744_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(v_e_743_);
    v_r_745_ = crate::leanh::lean_box((v_res_744_) as usize);
    return v_r_745_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__0(
    mut v___y_746_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_747_ = l_Lean_Meta_Sym_getNatValue_x3f(v___y_746_);
    if crate::leanh::lean_obj_tag(v___x_747_) == 0 {
        let mut v___x_748_: u8 = 0;
        v___x_748_ = 0;
        return v___x_748_;
    } else {
        let mut v___x_749_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_747_, 1);
        v___x_749_ = 1;
        return v___x_749_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed(
    mut v___y_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_751_: u8 = 0;
    let mut v_r_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_751_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__0(v___y_750_);
    v_r_752_ = crate::leanh::lean_box((v_res_751_) as usize);
    return v_r_752_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__1(
    mut v___y_753_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_754_ = l_Lean_Meta_Sym_getStringValue_x3f(v___y_753_);
    if crate::leanh::lean_obj_tag(v___x_754_) == 0 {
        let mut v___x_755_: u8 = 0;
        v___x_755_ = 0;
        return v___x_755_;
    } else {
        let mut v___x_756_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_754_, 1);
        v___x_756_ = 1;
        return v___x_756_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed(
    mut v___y_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_758_: u8 = 0;
    let mut v_r_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_758_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__1(v___y_757_);
    v_r_759_ = crate::leanh::lean_box((v_res_758_) as usize);
    return v_r_759_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__2(
    mut v___y_760_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = l_Lean_Meta_Sym_getIntValue_x3f(v___y_760_);
    if crate::leanh::lean_obj_tag(v___x_761_) == 0 {
        let mut v___x_762_: u8 = 0;
        v___x_762_ = 0;
        return v___x_762_;
    } else {
        let mut v___x_763_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_761_, 1);
        v___x_763_ = 1;
        return v___x_763_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed(
    mut v___y_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_765_: u8 = 0;
    let mut v_r_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_765_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__2(v___y_764_);
    v_r_766_ = crate::leanh::lean_box((v_res_765_) as usize);
    return v_r_766_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__3(
    mut v___y_767_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v___y_767_);
    if crate::leanh::lean_obj_tag(v___x_768_) == 0 {
        let mut v___x_769_: u8 = 0;
        v___x_769_ = 0;
        return v___x_769_;
    } else {
        let mut v___x_770_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_768_, 1);
        v___x_770_ = 1;
        return v___x_770_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed(
    mut v___y_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_772_: u8 = 0;
    let mut v_r_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_772_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__3(v___y_771_);
    v_r_773_ = crate::leanh::lean_box((v_res_772_) as usize);
    return v_r_773_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__4(
    mut v___y_774_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_775_ = l_Lean_Meta_Sym_getFinValue_x3f(v___y_774_);
    if crate::leanh::lean_obj_tag(v___x_775_) == 0 {
        let mut v___x_776_: u8 = 0;
        v___x_776_ = 0;
        return v___x_776_;
    } else {
        let mut v___x_777_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_775_, 1);
        v___x_777_ = 1;
        return v___x_777_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed(
    mut v___y_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_779_: u8 = 0;
    let mut v_r_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_779_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__4(v___y_778_);
    v_r_780_ = crate::leanh::lean_box((v_res_779_) as usize);
    return v_r_780_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__5(
    mut v___y_781_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_782_ = l_Lean_Meta_Sym_getCharValue_x3f(v___y_781_);
    if crate::leanh::lean_obj_tag(v___x_782_) == 0 {
        let mut v___x_783_: u8 = 0;
        v___x_783_ = 0;
        return v___x_783_;
    } else {
        let mut v___x_784_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_782_, 1);
        v___x_784_ = 1;
        return v___x_784_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed(
    mut v___y_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_786_: u8 = 0;
    let mut v_r_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__5(v___y_785_);
    v_r_787_ = crate::leanh::lean_box((v_res_786_) as usize);
    return v_r_787_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__6(
    mut v___y_788_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_789_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v___y_788_);
    if crate::leanh::lean_obj_tag(v___x_789_) == 0 {
        let mut v___x_790_: u8 = 0;
        v___x_790_ = 0;
        return v___x_790_;
    } else {
        let mut v___x_791_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_789_, 1);
        v___x_791_ = 1;
        return v___x_791_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed(
    mut v___y_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_793_: u8 = 0;
    let mut v_r_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_793_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__6(v___y_792_);
    v_r_794_ = crate::leanh::lean_box((v_res_793_) as usize);
    return v_r_794_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__7(
    mut v___y_795_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_796_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v___y_795_);
    if crate::leanh::lean_obj_tag(v___x_796_) == 0 {
        let mut v___x_797_: u8 = 0;
        v___x_797_ = 0;
        return v___x_797_;
    } else {
        let mut v___x_798_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_796_, 1);
        v___x_798_ = 1;
        return v___x_798_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed(
    mut v___y_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_800_: u8 = 0;
    let mut v_r_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_800_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__7(v___y_799_);
    v_r_801_ = crate::leanh::lean_box((v_res_800_) as usize);
    return v_r_801_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__8(
    mut v___y_802_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_803_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v___y_802_);
    if crate::leanh::lean_obj_tag(v___x_803_) == 0 {
        let mut v___x_804_: u8 = 0;
        v___x_804_ = 0;
        return v___x_804_;
    } else {
        let mut v___x_805_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_803_, 1);
        v___x_805_ = 1;
        return v___x_805_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed(
    mut v___y_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_807_: u8 = 0;
    let mut v_r_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_807_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__8(v___y_806_);
    v_r_808_ = crate::leanh::lean_box((v_res_807_) as usize);
    return v_r_808_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__9(
    mut v___y_809_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v___y_809_);
    if crate::leanh::lean_obj_tag(v___x_810_) == 0 {
        let mut v___x_811_: u8 = 0;
        v___x_811_ = 0;
        return v___x_811_;
    } else {
        let mut v___x_812_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_810_, 1);
        v___x_812_ = 1;
        return v___x_812_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed(
    mut v___y_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_814_: u8 = 0;
    let mut v_r_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__9(v___y_813_);
    v_r_815_ = crate::leanh::lean_box((v_res_814_) as usize);
    return v_r_815_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__10(
    mut v___y_816_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = l_Lean_Meta_Sym_getInt8Value_x3f(v___y_816_);
    if crate::leanh::lean_obj_tag(v___x_817_) == 0 {
        let mut v___x_818_: u8 = 0;
        v___x_818_ = 0;
        return v___x_818_;
    } else {
        let mut v___x_819_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_817_, 1);
        v___x_819_ = 1;
        return v___x_819_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed(
    mut v___y_820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_821_: u8 = 0;
    let mut v_r_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_821_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__10(v___y_820_);
    v_r_822_ = crate::leanh::lean_box((v_res_821_) as usize);
    return v_r_822_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__11(
    mut v___y_823_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = l_Lean_Meta_Sym_getInt16Value_x3f(v___y_823_);
    if crate::leanh::lean_obj_tag(v___x_824_) == 0 {
        let mut v___x_825_: u8 = 0;
        v___x_825_ = 0;
        return v___x_825_;
    } else {
        let mut v___x_826_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_824_, 1);
        v___x_826_ = 1;
        return v___x_826_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed(
    mut v___y_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_828_: u8 = 0;
    let mut v_r_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_828_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__11(v___y_827_);
    v_r_829_ = crate::leanh::lean_box((v_res_828_) as usize);
    return v_r_829_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__12(
    mut v___y_830_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_Meta_Sym_getInt32Value_x3f(v___y_830_);
    if crate::leanh::lean_obj_tag(v___x_831_) == 0 {
        let mut v___x_832_: u8 = 0;
        v___x_832_ = 0;
        return v___x_832_;
    } else {
        let mut v___x_833_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_831_, 1);
        v___x_833_ = 1;
        return v___x_833_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed(
    mut v___y_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_835_: u8 = 0;
    let mut v_r_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__12(v___y_834_);
    v_r_836_ = crate::leanh::lean_box((v_res_835_) as usize);
    return v_r_836_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__13(
    mut v___y_837_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = l_Lean_Meta_Sym_getInt64Value_x3f(v___y_837_);
    if crate::leanh::lean_obj_tag(v___x_838_) == 0 {
        let mut v___x_839_: u8 = 0;
        v___x_839_ = 0;
        return v___x_839_;
    } else {
        let mut v___x_840_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_838_, 1);
        v___x_840_ = 1;
        return v___x_840_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed(
    mut v___y_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_842_: u8 = 0;
    let mut v_r_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_842_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__13(v___y_841_);
    v_r_843_ = crate::leanh::lean_box((v_res_842_) as usize);
    return v_r_843_;
}
pub unsafe fn l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(
    mut v_e_844_: *mut crate::leanh::LeanObject,
    mut v_x_845_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_846_: u8 = 0;
    let mut v_head_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: u8 = 0;
    let mut v___x_852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_845_) == 0 {
                    crate::leanh::lean_dec_ref(v_e_844_);
                    v___x_846_ = 0;
                    return v___x_846_;
                } else {
                    v_head_847_ = crate::leanh::lean_ctor_get(v_x_845_, 0);
                    crate::leanh::lean_inc(v_head_847_);
                    v_tail_848_ = crate::leanh::lean_ctor_get(v_x_845_, 1);
                    crate::leanh::lean_inc(v_tail_848_);
                    crate::leanh::lean_dec_ref_known(v_x_845_, 2);
                    crate::leanh::lean_inc_ref(v_e_844_);
                    v___x_849_ = crate::leanh::lean_apply_1(v_head_847_, v_e_844_);
                    v___x_850_ = (crate::leanh::lean_unbox(v___x_849_) as u8);
                    if v___x_850_ == 0 {
                        v_x_845_ = v_tail_848_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_848_);
                        crate::leanh::lean_dec_ref(v_e_844_);
                        v___x_852_ = (crate::leanh::lean_unbox(v___x_849_) as u8);
                        return v___x_852_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0___boxed(
    mut v_e_853_: *mut crate::leanh::LeanObject,
    mut v_x_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_855_: u8 = 0;
    let mut v_r_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_855_ = l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(v_e_853_, v_x_854_);
    v_r_856_ = crate::leanh::lean_box((v_res_855_) as usize);
    return v_r_856_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal(mut v_e_913_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    v___x_914_ = l_Lean_Meta_Tactic_Cbv_isVal___closed__27;
    v___x_915_ = l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(v_e_913_, v___x_914_);
    return v___x_915_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isVal___boxed(
    mut v_e_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_917_: u8 = 0;
    let mut v_r_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_917_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_916_);
    v_r_918_ = crate::leanh::lean_box((v_res_917_) as usize);
    return v_r_918_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(
    mut v_e_919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_921_: u8 = 0;
    let mut v___x_922_: u8 = 0;
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_919_);
    v___x_922_ = 0;
    v___x_923_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_923_, 0 as u32, v___x_921_);
    crate::leanh::lean_ctor_set_uint8(v___x_923_, 1 as u32, v___x_922_);
    v___x_924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_924_, 0, v___x_923_);
    return v___x_924_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg___boxed(
    mut v_e_925_: *mut crate::leanh::LeanObject,
    mut v_a_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_927_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_925_);
    return v_res_927_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isBuiltinValue(
    mut v_e_928_: *mut crate::leanh::LeanObject,
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
    mut v_a_932_: *mut crate::leanh::LeanObject,
    mut v_a_933_: *mut crate::leanh::LeanObject,
    mut v_a_934_: *mut crate::leanh::LeanObject,
    mut v_a_935_: *mut crate::leanh::LeanObject,
    mut v_a_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_939_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_928_);
    return v___x_939_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isBuiltinValue___boxed(
    mut v_e_940_: *mut crate::leanh::LeanObject,
    mut v_a_941_: *mut crate::leanh::LeanObject,
    mut v_a_942_: *mut crate::leanh::LeanObject,
    mut v_a_943_: *mut crate::leanh::LeanObject,
    mut v_a_944_: *mut crate::leanh::LeanObject,
    mut v_a_945_: *mut crate::leanh::LeanObject,
    mut v_a_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
    mut v_a_948_: *mut crate::leanh::LeanObject,
    mut v_a_949_: *mut crate::leanh::LeanObject,
    mut v_a_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue(
        v_e_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_,
        v_a_949_,
    );
    crate::leanh::lean_dec(v_a_949_);
    crate::leanh::lean_dec_ref(v_a_948_);
    crate::leanh::lean_dec(v_a_947_);
    crate::leanh::lean_dec_ref(v_a_946_);
    crate::leanh::lean_dec(v_a_945_);
    crate::leanh::lean_dec_ref(v_a_944_);
    crate::leanh::lean_dec(v_a_943_);
    crate::leanh::lean_dec_ref(v_a_942_);
    crate::leanh::lean_dec(v_a_941_);
    return v_res_951_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_guardSimproc(
    mut v_p_952_: *mut crate::leanh::LeanObject,
    mut v_s_953_: *mut crate::leanh::LeanObject,
    mut v_e_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
    mut v_a_956_: *mut crate::leanh::LeanObject,
    mut v_a_957_: *mut crate::leanh::LeanObject,
    mut v_a_958_: *mut crate::leanh::LeanObject,
    mut v_a_959_: *mut crate::leanh::LeanObject,
    mut v_a_960_: *mut crate::leanh::LeanObject,
    mut v_a_961_: *mut crate::leanh::LeanObject,
    mut v_a_962_: *mut crate::leanh::LeanObject,
    mut v_a_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: u8 = 0;
    crate::leanh::lean_inc_ref(v_e_954_);
    v___x_965_ = crate::leanh::lean_apply_1(v_p_952_, v_e_954_);
    v___x_966_ = (crate::leanh::lean_unbox(v___x_965_) as u8);
    if v___x_966_ == 0 {
        let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_968_: u8 = 0;
        let mut v___x_969_: u8 = 0;
        let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_954_);
        crate::leanh::lean_dec_ref(v_s_953_);
        v___x_967_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
        v___x_968_ = (crate::leanh::lean_unbox(v___x_965_) as u8);
        crate::leanh::lean_ctor_set_uint8(v___x_967_, 0 as u32, v___x_968_);
        v___x_969_ = (crate::leanh::lean_unbox(v___x_965_) as u8);
        crate::leanh::lean_ctor_set_uint8(v___x_967_, 1 as u32, v___x_969_);
        v___x_970_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_970_, 0, v___x_967_);
        return v___x_970_;
    } else {
        let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_a_963_);
        crate::leanh::lean_inc_ref(v_a_962_);
        crate::leanh::lean_inc(v_a_961_);
        crate::leanh::lean_inc_ref(v_a_960_);
        crate::leanh::lean_inc(v_a_959_);
        crate::leanh::lean_inc_ref(v_a_958_);
        crate::leanh::lean_inc(v_a_957_);
        crate::leanh::lean_inc_ref(v_a_956_);
        crate::leanh::lean_inc(v_a_955_);
        v___x_971_ = crate::leanh::lean_apply_11(
            v_s_953_,
            v_e_954_,
            v_a_955_,
            v_a_956_,
            v_a_957_,
            v_a_958_,
            v_a_959_,
            v_a_960_,
            v_a_961_,
            v_a_962_,
            v_a_963_,
            crate::leanh::lean_box(0),
        );
        return v___x_971_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_guardSimproc___boxed(
    mut v_p_972_: *mut crate::leanh::LeanObject,
    mut v_s_973_: *mut crate::leanh::LeanObject,
    mut v_e_974_: *mut crate::leanh::LeanObject,
    mut v_a_975_: *mut crate::leanh::LeanObject,
    mut v_a_976_: *mut crate::leanh::LeanObject,
    mut v_a_977_: *mut crate::leanh::LeanObject,
    mut v_a_978_: *mut crate::leanh::LeanObject,
    mut v_a_979_: *mut crate::leanh::LeanObject,
    mut v_a_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
    mut v_a_982_: *mut crate::leanh::LeanObject,
    mut v_a_983_: *mut crate::leanh::LeanObject,
    mut v_a_984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_985_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(
        v_p_972_, v_s_973_, v_e_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_,
        v_a_981_, v_a_982_, v_a_983_,
    );
    crate::leanh::lean_dec(v_a_983_);
    crate::leanh::lean_dec_ref(v_a_982_);
    crate::leanh::lean_dec(v_a_981_);
    crate::leanh::lean_dec_ref(v_a_980_);
    crate::leanh::lean_dec(v_a_979_);
    crate::leanh::lean_dec_ref(v_a_978_);
    crate::leanh::lean_dec(v_a_977_);
    crate::leanh::lean_dec_ref(v_a_976_);
    crate::leanh::lean_dec(v_a_975_);
    return v_res_985_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(
    mut v_x_986_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_987_: u8 = 0;
    let mut v_a_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    let mut v_a_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_x_986_) {
                    0 => {
                        v___x_987_ = 1;
                        return v___x_987_;
                    }
                    2 => {
                        v_a_988_ = crate::leanh::lean_ctor_get(v_x_986_, 0);
                        v_a_989_ = crate::leanh::lean_ctor_get(v_x_986_, 1);
                        v___x_990_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_988_);
                        if v___x_990_ == 0 {
                            return v___x_990_;
                        } else {
                            v_x_986_ = v_a_989_;
                            state = 0;
                            continue;
                        }
                    }
                    3 => {
                        v_a_992_ = crate::leanh::lean_ctor_get(v_x_986_, 1);
                        v_x_986_ = v_a_992_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        v___x_994_ = 0;
                        return v___x_994_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero___boxed(
    mut v_x_995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_996_: u8 = 0;
    let mut v_r_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_996_ =
        l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_x_995_);
    crate::leanh::lean_dec(v_x_995_);
    v_r_997_ = crate::leanh::lean_box((v_res_996_) as usize);
    return v_r_997_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(
    mut v_l_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1013_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1019_: u8 = 0;
    let mut v_unused_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1001_ = lean_st_ref_get(v___y_999_);
                v_mctx_1002_ = crate::leanh::lean_ctor_get(v___x_1001_, 0);
                crate::leanh::lean_inc_ref(v_mctx_1002_);
                crate::leanh::lean_dec(v___x_1001_);
                v___x_1003_ = lean_instantiate_level_mvars(v_mctx_1002_, v_l_998_);
                v_fst_1004_ = crate::leanh::lean_ctor_get(v___x_1003_, 0);
                crate::leanh::lean_inc(v_fst_1004_);
                v_snd_1005_ = crate::leanh::lean_ctor_get(v___x_1003_, 1);
                crate::leanh::lean_inc(v_snd_1005_);
                crate::leanh::lean_dec_ref(v___x_1003_);
                v___x_1006_ = lean_st_ref_take(v___y_999_);
                v_cache_1007_ = crate::leanh::lean_ctor_get(v___x_1006_, 1);
                v_zetaDeltaFVarIds_1008_ = crate::leanh::lean_ctor_get(v___x_1006_, 2);
                v_postponed_1009_ = crate::leanh::lean_ctor_get(v___x_1006_, 3);
                v_diag_1010_ = crate::leanh::lean_ctor_get(v___x_1006_, 4);
                v_isSharedCheck_1019_ = (!crate::leanh::lean_is_exclusive(v___x_1006_)) as u8;
                if v_isSharedCheck_1019_ == 0 {
                    v_unused_1020_ = crate::leanh::lean_ctor_get(v___x_1006_, 0);
                    crate::leanh::lean_dec(v_unused_1020_);
                    v___x_1012_ = v___x_1006_;
                    v_isShared_1013_ = v_isSharedCheck_1019_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1010_);
                    crate::leanh::lean_inc(v_postponed_1009_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1008_);
                    crate::leanh::lean_inc(v_cache_1007_);
                    crate::leanh::lean_dec(v___x_1006_);
                    v___x_1012_ = crate::leanh::lean_box(0);
                    v_isShared_1013_ = v_isSharedCheck_1019_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1013_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1012_, 0, v_fst_1004_);
                    v___x_1015_ = v___x_1012_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_fst_1004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_cache_1007_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1018_,
                        2,
                        v_zetaDeltaFVarIds_1008_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 3, v_postponed_1009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 4, v_diag_1010_);
                    v___x_1015_ = v_reuseFailAlloc_1018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1016_ = lean_st_ref_set(v___y_999_, v___x_1015_);
                v___x_1017_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1017_, 0, v_snd_1005_);
                return v___x_1017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg___boxed(
    mut v_l_1021_: *mut crate::leanh::LeanObject,
    mut v___y_1022_: *mut crate::leanh::LeanObject,
    mut v___y_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1024_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_1021_, v___y_1022_);
    crate::leanh::lean_dec(v___y_1022_);
    return v_res_1024_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(
    mut v_l_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
    mut v___y_1028_: *mut crate::leanh::LeanObject,
    mut v___y_1029_: *mut crate::leanh::LeanObject,
    mut v___y_1030_: *mut crate::leanh::LeanObject,
    mut v___y_1031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_1025_, v___y_1029_);
    return v___x_1033_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___boxed(
    mut v_l_1034_: *mut crate::leanh::LeanObject,
    mut v___y_1035_: *mut crate::leanh::LeanObject,
    mut v___y_1036_: *mut crate::leanh::LeanObject,
    mut v___y_1037_: *mut crate::leanh::LeanObject,
    mut v___y_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
    mut v___y_1040_: *mut crate::leanh::LeanObject,
    mut v___y_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(v_l_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
    crate::leanh::lean_dec(v___y_1040_);
    crate::leanh::lean_dec_ref(v___y_1039_);
    crate::leanh::lean_dec(v___y_1038_);
    crate::leanh::lean_dec_ref(v___y_1037_);
    crate::leanh::lean_dec(v___y_1036_);
    crate::leanh::lean_dec_ref(v___y_1035_);
    return v_res_1042_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(
    mut v_e_1043_: *mut crate::leanh::LeanObject,
    mut v_a_1044_: *mut crate::leanh::LeanObject,
    mut v_a_1045_: *mut crate::leanh::LeanObject,
    mut v_a_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
    mut v_a_1048_: *mut crate::leanh::LeanObject,
    mut v_a_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1056_: u8 = 0;
    let mut v___x_1057_: u8 = 0;
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1073_: u8 = 0;
    let mut v_u_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1079_: u8 = 0;
    let mut v___x_1080_: u8 = 0;
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1091_: u8 = 0;
    let mut v_a_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v_a_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1103_: u8 = 0;
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut v_a_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1112_: u8 = 0;
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1043_);
                v___x_1051_ =
                    l_Lean_Meta_isPropQuick(v_e_1043_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
                if crate::leanh::lean_obj_tag(v___x_1051_) == 0 {
                    v_a_1052_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                    v_isSharedCheck_1108_ = (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                    if v_isSharedCheck_1108_ == 0 {
                        v___x_1054_ = v___x_1051_;
                        v_isShared_1055_ = v_isSharedCheck_1108_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1052_);
                        crate::leanh::lean_dec(v___x_1051_);
                        v___x_1054_ = crate::leanh::lean_box(0);
                        v_isShared_1055_ = v_isSharedCheck_1108_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1043_);
                    v_a_1109_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                    v_isSharedCheck_1116_ = (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                    if v_isSharedCheck_1116_ == 0 {
                        v___x_1111_ = v___x_1051_;
                        v_isShared_1112_ = v_isSharedCheck_1116_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1109_);
                        crate::leanh::lean_dec(v___x_1051_);
                        v___x_1111_ = crate::leanh::lean_box(0);
                        v_isShared_1112_ = v_isSharedCheck_1116_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1056_ = (crate::leanh::lean_unbox(v_a_1052_) as u8);
                crate::leanh::lean_dec(v_a_1052_);
                match v___x_1056_ {
                    0 => {
                        crate::leanh::lean_dec_ref(v_e_1043_);
                        v___x_1057_ = 0;
                        v___x_1058_ = crate::leanh::lean_box((v___x_1057_) as usize);
                        if v_isShared_1055_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1054_, 0, v___x_1058_);
                            v___x_1060_ = v___x_1054_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1061_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
                            v___x_1060_ = v_reuseFailAlloc_1061_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_e_1043_);
                        v___x_1062_ = 1;
                        v___x_1063_ = crate::leanh::lean_box((v___x_1062_) as usize);
                        if v_isShared_1055_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1054_, 0, v___x_1063_);
                            v___x_1065_ = v___x_1054_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1066_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
                            v___x_1065_ = v_reuseFailAlloc_1066_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_1054_);
                        v___x_1067_ = l_Lean_Meta_Sym_inferType___redArg(
                            v_e_1043_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1067_) == 0 {
                            v_a_1068_ = crate::leanh::lean_ctor_get(v___x_1067_, 0);
                            crate::leanh::lean_inc(v_a_1068_);
                            crate::leanh::lean_dec_ref_known(v___x_1067_, 1);
                            v___x_1069_ = l_Lean_Meta_whnfD(
                                v_a_1068_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1069_) == 0 {
                                v_a_1070_ = crate::leanh::lean_ctor_get(v___x_1069_, 0);
                                v_isSharedCheck_1091_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1069_)) as u8;
                                if v_isSharedCheck_1091_ == 0 {
                                    v___x_1072_ = v___x_1069_;
                                    v_isShared_1073_ = v_isSharedCheck_1091_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1070_);
                                    crate::leanh::lean_dec(v___x_1069_);
                                    v___x_1072_ = crate::leanh::lean_box(0);
                                    v_isShared_1073_ = v_isSharedCheck_1091_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_a_1092_ = crate::leanh::lean_ctor_get(v___x_1069_, 0);
                                v_isSharedCheck_1099_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1069_)) as u8;
                                if v_isSharedCheck_1099_ == 0 {
                                    v___x_1094_ = v___x_1069_;
                                    v_isShared_1095_ = v_isSharedCheck_1099_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1092_);
                                    crate::leanh::lean_dec(v___x_1069_);
                                    v___x_1094_ = crate::leanh::lean_box(0);
                                    v_isShared_1095_ = v_isSharedCheck_1099_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            v_a_1100_ = crate::leanh::lean_ctor_get(v___x_1067_, 0);
                            v_isSharedCheck_1107_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1067_)) as u8;
                            if v_isSharedCheck_1107_ == 0 {
                                v___x_1102_ = v___x_1067_;
                                v_isShared_1103_ = v_isSharedCheck_1107_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1100_);
                                crate::leanh::lean_dec(v___x_1067_);
                                v___x_1102_ = crate::leanh::lean_box(0);
                                v_isShared_1103_ = v_isSharedCheck_1107_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1060_;
            }
            3 => {
                return v___x_1065_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_1070_) == 3 {
                    crate::leanh::lean_del_object(v___x_1072_);
                    v_u_1074_ = crate::leanh::lean_ctor_get(v_a_1070_, 0);
                    crate::leanh::lean_inc(v_u_1074_);
                    crate::leanh::lean_dec_ref_known(v_a_1070_, 1);
                    v___x_1075_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_u_1074_, v_a_1047_);
                    v_a_1076_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
                    v_isSharedCheck_1085_ = (!crate::leanh::lean_is_exclusive(v___x_1075_)) as u8;
                    if v_isSharedCheck_1085_ == 0 {
                        v___x_1078_ = v___x_1075_;
                        v_isShared_1079_ = v_isSharedCheck_1085_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1076_);
                        crate::leanh::lean_dec(v___x_1075_);
                        v___x_1078_ = crate::leanh::lean_box(0);
                        v_isShared_1079_ = v_isSharedCheck_1085_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1070_);
                    v___x_1086_ = 0;
                    v___x_1087_ = crate::leanh::lean_box((v___x_1086_) as usize);
                    if v_isShared_1073_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1087_);
                        v___x_1089_ = v___x_1072_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1090_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
                        v___x_1089_ = v_reuseFailAlloc_1090_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1080_ =
                    l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(
                        v_a_1076_,
                    );
                crate::leanh::lean_dec(v_a_1076_);
                v___x_1081_ = crate::leanh::lean_box((v___x_1080_) as usize);
                if v_isShared_1079_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1078_, 0, v___x_1081_);
                    v___x_1083_ = v___x_1078_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
                    v___x_1083_ = v_reuseFailAlloc_1084_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1083_;
            }
            7 => {
                return v___x_1089_;
            }
            8 => {
                if v_isShared_1095_ == 0 {
                    v___x_1097_ = v___x_1094_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
                    v___x_1097_ = v_reuseFailAlloc_1098_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1097_;
            }
            10 => {
                if v_isShared_1103_ == 0 {
                    v___x_1105_ = v___x_1102_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
                    v___x_1105_ = v_reuseFailAlloc_1106_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1105_;
            }
            12 => {
                if v_isShared_1112_ == 0 {
                    v___x_1114_ = v___x_1111_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
                    v___x_1114_ = v_reuseFailAlloc_1115_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp___boxed(
    mut v_e_1117_: *mut crate::leanh::LeanObject,
    mut v_a_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1125_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(
        v_e_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_,
    );
    crate::leanh::lean_dec(v_a_1123_);
    crate::leanh::lean_dec_ref(v_a_1122_);
    crate::leanh::lean_dec(v_a_1121_);
    crate::leanh::lean_dec_ref(v_a_1120_);
    crate::leanh::lean_dec(v_a_1119_);
    crate::leanh::lean_dec_ref(v_a_1118_);
    return v_res_1125_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(
    mut v_e_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
    mut v_a_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
    mut v_a_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1138_: u8 = 0;
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: u8 = 0;
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u8 = 0;
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut v_isSharedCheck_1161_: u8 = 0;
    let mut v_a_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1126_);
                v___x_1134_ =
                    l_Lean_Meta_isProofQuick(v_e_1126_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
                if crate::leanh::lean_obj_tag(v___x_1134_) == 0 {
                    v_a_1135_ = crate::leanh::lean_ctor_get(v___x_1134_, 0);
                    v_isSharedCheck_1161_ = (!crate::leanh::lean_is_exclusive(v___x_1134_)) as u8;
                    if v_isSharedCheck_1161_ == 0 {
                        v___x_1137_ = v___x_1134_;
                        v_isShared_1138_ = v_isSharedCheck_1161_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1135_);
                        crate::leanh::lean_dec(v___x_1134_);
                        v___x_1137_ = crate::leanh::lean_box(0);
                        v_isShared_1138_ = v_isSharedCheck_1161_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1126_);
                    v_a_1162_ = crate::leanh::lean_ctor_get(v___x_1134_, 0);
                    v_isSharedCheck_1169_ = (!crate::leanh::lean_is_exclusive(v___x_1134_)) as u8;
                    if v_isSharedCheck_1169_ == 0 {
                        v___x_1164_ = v___x_1134_;
                        v_isShared_1165_ = v_isSharedCheck_1169_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1162_);
                        crate::leanh::lean_dec(v___x_1134_);
                        v___x_1164_ = crate::leanh::lean_box(0);
                        v_isShared_1165_ = v_isSharedCheck_1169_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1139_ = (crate::leanh::lean_unbox(v_a_1135_) as u8);
                crate::leanh::lean_dec(v_a_1135_);
                match v___x_1139_ {
                    0 => {
                        crate::leanh::lean_dec_ref(v_e_1126_);
                        v___x_1140_ = 0;
                        v___x_1141_ = crate::leanh::lean_box((v___x_1140_) as usize);
                        if v_isShared_1138_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1137_, 0, v___x_1141_);
                            v___x_1143_ = v___x_1137_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1144_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
                            v___x_1143_ = v_reuseFailAlloc_1144_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_e_1126_);
                        v___x_1145_ = 1;
                        v___x_1146_ = crate::leanh::lean_box((v___x_1145_) as usize);
                        if v_isShared_1138_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1137_, 0, v___x_1146_);
                            v___x_1148_ = v___x_1137_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1149_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
                            v___x_1148_ = v_reuseFailAlloc_1149_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_1137_);
                        v___x_1150_ = l_Lean_Meta_Sym_inferType___redArg(
                            v_e_1126_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1150_) == 0 {
                            v_a_1151_ = crate::leanh::lean_ctor_get(v___x_1150_, 0);
                            crate::leanh::lean_inc(v_a_1151_);
                            crate::leanh::lean_dec_ref_known(v___x_1150_, 1);
                            v___x_1152_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_a_1151_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
                            return v___x_1152_;
                        } else {
                            v_a_1153_ = crate::leanh::lean_ctor_get(v___x_1150_, 0);
                            v_isSharedCheck_1160_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1150_)) as u8;
                            if v_isSharedCheck_1160_ == 0 {
                                v___x_1155_ = v___x_1150_;
                                v_isShared_1156_ = v_isSharedCheck_1160_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1153_);
                                crate::leanh::lean_dec(v___x_1150_);
                                v___x_1155_ = crate::leanh::lean_box(0);
                                v_isShared_1156_ = v_isSharedCheck_1160_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1143_;
            }
            3 => {
                return v___x_1148_;
            }
            4 => {
                if v_isShared_1156_ == 0 {
                    v___x_1158_ = v___x_1155_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
                    v___x_1158_ = v_reuseFailAlloc_1159_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1158_;
            }
            6 => {
                if v_isShared_1165_ == 0 {
                    v___x_1167_ = v___x_1164_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
                    v___x_1167_ = v_reuseFailAlloc_1168_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof___boxed(
    mut v_e_1170_: *mut crate::leanh::LeanObject,
    mut v_a_1171_: *mut crate::leanh::LeanObject,
    mut v_a_1172_: *mut crate::leanh::LeanObject,
    mut v_a_1173_: *mut crate::leanh::LeanObject,
    mut v_a_1174_: *mut crate::leanh::LeanObject,
    mut v_a_1175_: *mut crate::leanh::LeanObject,
    mut v_a_1176_: *mut crate::leanh::LeanObject,
    mut v_a_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1178_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(
        v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_,
    );
    crate::leanh::lean_dec(v_a_1176_);
    crate::leanh::lean_dec_ref(v_a_1175_);
    crate::leanh::lean_dec(v_a_1174_);
    crate::leanh::lean_dec_ref(v_a_1173_);
    crate::leanh::lean_dec(v_a_1172_);
    crate::leanh::lean_dec_ref(v_a_1171_);
    return v_res_1178_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(
    mut v_e_1179_: *mut crate::leanh::LeanObject,
    mut v_a_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_a_1182_: *mut crate::leanh::LeanObject,
    mut v_a_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: u8 = 0;
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1198_: u8 = 0;
    let mut v_a_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1202_: u8 = 0;
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1187_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(
                    v_e_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_,
                );
                if crate::leanh::lean_obj_tag(v___x_1187_) == 0 {
                    v_a_1188_ = crate::leanh::lean_ctor_get(v___x_1187_, 0);
                    v_isSharedCheck_1198_ = (!crate::leanh::lean_is_exclusive(v___x_1187_)) as u8;
                    if v_isSharedCheck_1198_ == 0 {
                        v___x_1190_ = v___x_1187_;
                        v_isShared_1191_ = v_isSharedCheck_1198_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1188_);
                        crate::leanh::lean_dec(v___x_1187_);
                        v___x_1190_ = crate::leanh::lean_box(0);
                        v_isShared_1191_ = v_isSharedCheck_1198_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1199_ = crate::leanh::lean_ctor_get(v___x_1187_, 0);
                    v_isSharedCheck_1206_ = (!crate::leanh::lean_is_exclusive(v___x_1187_)) as u8;
                    if v_isSharedCheck_1206_ == 0 {
                        v___x_1201_ = v___x_1187_;
                        v_isShared_1202_ = v_isSharedCheck_1206_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1199_);
                        crate::leanh::lean_dec(v___x_1187_);
                        v___x_1201_ = crate::leanh::lean_box(0);
                        v_isShared_1202_ = v_isSharedCheck_1206_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1192_ = 0;
                v___x_1193_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                v___x_1194_ = (crate::leanh::lean_unbox(v_a_1188_) as u8);
                crate::leanh::lean_dec(v_a_1188_);
                crate::leanh::lean_ctor_set_uint8(v___x_1193_, 0 as u32, v___x_1194_);
                crate::leanh::lean_ctor_set_uint8(v___x_1193_, 1 as u32, v___x_1192_);
                if v_isShared_1191_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1190_, 0, v___x_1193_);
                    v___x_1196_ = v___x_1190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1193_);
                    v___x_1196_ = v_reuseFailAlloc_1197_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1196_;
            }
            3 => {
                if v_isShared_1202_ == 0 {
                    v___x_1204_ = v___x_1201_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1205_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
                    v___x_1204_ = v_reuseFailAlloc_1205_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg___boxed(
    mut v_e_1207_: *mut crate::leanh::LeanObject,
    mut v_a_1208_: *mut crate::leanh::LeanObject,
    mut v_a_1209_: *mut crate::leanh::LeanObject,
    mut v_a_1210_: *mut crate::leanh::LeanObject,
    mut v_a_1211_: *mut crate::leanh::LeanObject,
    mut v_a_1212_: *mut crate::leanh::LeanObject,
    mut v_a_1213_: *mut crate::leanh::LeanObject,
    mut v_a_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1215_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(
        v_e_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_,
    );
    crate::leanh::lean_dec(v_a_1213_);
    crate::leanh::lean_dec_ref(v_a_1212_);
    crate::leanh::lean_dec(v_a_1211_);
    crate::leanh::lean_dec_ref(v_a_1210_);
    crate::leanh::lean_dec(v_a_1209_);
    crate::leanh::lean_dec_ref(v_a_1208_);
    return v_res_1215_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isProofTerm(
    mut v_e_1216_: *mut crate::leanh::LeanObject,
    mut v_a_1217_: *mut crate::leanh::LeanObject,
    mut v_a_1218_: *mut crate::leanh::LeanObject,
    mut v_a_1219_: *mut crate::leanh::LeanObject,
    mut v_a_1220_: *mut crate::leanh::LeanObject,
    mut v_a_1221_: *mut crate::leanh::LeanObject,
    mut v_a_1222_: *mut crate::leanh::LeanObject,
    mut v_a_1223_: *mut crate::leanh::LeanObject,
    mut v_a_1224_: *mut crate::leanh::LeanObject,
    mut v_a_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(
        v_e_1216_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_,
    );
    return v___x_1227_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isProofTerm___boxed(
    mut v_e_1228_: *mut crate::leanh::LeanObject,
    mut v_a_1229_: *mut crate::leanh::LeanObject,
    mut v_a_1230_: *mut crate::leanh::LeanObject,
    mut v_a_1231_: *mut crate::leanh::LeanObject,
    mut v_a_1232_: *mut crate::leanh::LeanObject,
    mut v_a_1233_: *mut crate::leanh::LeanObject,
    mut v_a_1234_: *mut crate::leanh::LeanObject,
    mut v_a_1235_: *mut crate::leanh::LeanObject,
    mut v_a_1236_: *mut crate::leanh::LeanObject,
    mut v_a_1237_: *mut crate::leanh::LeanObject,
    mut v_a_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Lean_Meta_Tactic_Cbv_isProofTerm(
        v_e_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_,
        v_a_1236_, v_a_1237_,
    );
    crate::leanh::lean_dec(v_a_1237_);
    crate::leanh::lean_dec_ref(v_a_1236_);
    crate::leanh::lean_dec(v_a_1235_);
    crate::leanh::lean_dec_ref(v_a_1234_);
    crate::leanh::lean_dec(v_a_1233_);
    crate::leanh::lean_dec_ref(v_a_1232_);
    crate::leanh::lean_dec(v_a_1231_);
    crate::leanh::lean_dec_ref(v_a_1230_);
    crate::leanh::lean_dec(v_a_1229_);
    return v_res_1239_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getListLitElems(
    mut v_e_1249_: *mut crate::leanh::LeanObject,
    mut v_acc_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: u8 = 0;
    let mut v___x_1258_: u8 = 0;
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: u8 = 0;
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1251_ = l_Lean_Expr_cleanupAnnotations(v_e_1249_);
                v___x_1252_ = l_Lean_Expr_isApp(v___x_1251_);
                if v___x_1252_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1251_);
                    crate::leanh::lean_dec_ref(v_acc_1250_);
                    v___x_1253_ = crate::leanh::lean_box(0);
                    return v___x_1253_;
                } else {
                    v_arg_1254_ = crate::leanh::lean_ctor_get(v___x_1251_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1254_);
                    v___x_1255_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1251_);
                    v___x_1256_ = l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2;
                    v___x_1257_ = l_Lean_Expr_isConstOf(v___x_1255_, v___x_1256_);
                    if v___x_1257_ == 0 {
                        v___x_1258_ = l_Lean_Expr_isApp(v___x_1255_);
                        if v___x_1258_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1255_);
                            crate::leanh::lean_dec_ref(v_arg_1254_);
                            crate::leanh::lean_dec_ref(v_acc_1250_);
                            v___x_1259_ = crate::leanh::lean_box(0);
                            return v___x_1259_;
                        } else {
                            v_arg_1260_ = crate::leanh::lean_ctor_get(v___x_1255_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1260_);
                            v___x_1261_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1255_);
                            v___x_1262_ = l_Lean_Expr_isApp(v___x_1261_);
                            if v___x_1262_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_1261_);
                                crate::leanh::lean_dec_ref(v_arg_1260_);
                                crate::leanh::lean_dec_ref(v_arg_1254_);
                                crate::leanh::lean_dec_ref(v_acc_1250_);
                                v___x_1263_ = crate::leanh::lean_box(0);
                                return v___x_1263_;
                            } else {
                                v___x_1264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1261_);
                                v___x_1265_ = l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4;
                                v___x_1266_ = l_Lean_Expr_isConstOf(v___x_1264_, v___x_1265_);
                                crate::leanh::lean_dec_ref(v___x_1264_);
                                if v___x_1266_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_1260_);
                                    crate::leanh::lean_dec_ref(v_arg_1254_);
                                    crate::leanh::lean_dec_ref(v_acc_1250_);
                                    v___x_1267_ = crate::leanh::lean_box(0);
                                    return v___x_1267_;
                                } else {
                                    v___x_1268_ = lean_array_push(v_acc_1250_, v_arg_1260_);
                                    v_e_1249_ = v_arg_1254_;
                                    v_acc_1250_ = v___x_1268_;
                                    state = 0;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1255_);
                        crate::leanh::lean_dec_ref(v_arg_1254_);
                        v___x_1270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1270_, 0, v_acc_1250_);
                        return v___x_1270_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(
    mut v_x_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_contextDependent_1272_: u8 = 0;
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1275_: u8 = 0;
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1271_) == 0 {
                    v_contextDependent_1272_ =
                        crate::leanh::lean_ctor_get_uint8(v_x_1271_, 1 as u32);
                    v_isSharedCheck_1280_ = (!crate::leanh::lean_is_exclusive(v_x_1271_)) as u8;
                    if v_isSharedCheck_1280_ == 0 {
                        v___x_1274_ = v_x_1271_;
                        v_isShared_1275_ = v_isSharedCheck_1280_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_1271_);
                        v___x_1274_ = crate::leanh::lean_box(0);
                        v_isShared_1275_ = v_isSharedCheck_1280_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_x_1271_;
                }
            }
            1 => {
                v___x_1276_ = 1;
                if v_isShared_1275_ == 0 {
                    v___x_1278_ = v___x_1274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1279_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1279_,
                        1 as u32,
                        v_contextDependent_1272_,
                    );
                    v___x_1278_ = v_reuseFailAlloc_1279_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v___x_1278_, 0 as u32, v___x_1276_);
                return v___x_1278_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
}
