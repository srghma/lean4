// Lean compiler output
// Module: Lean.Compiler.LCNF.ToExpr
// Imports: Lean.Compiler.LCNF.Basic Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_push,
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, l_Lean_Compiler_LCNF_Arg_toExpr___redArg,
    l_Lean_Compiler_LCNF_LetValue_toExpr, l_Lean_Compiler_LCNF_instInhabitedParam_default,
    runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_bvar___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_fvar___override, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNatLit,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg,
};
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__1_value:
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
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__2_value:
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
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__3_value:
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
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__4_value:
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
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__5_value:
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
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__6_value:
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
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10_value:
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
    m_fun: l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [99, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__0_value)
                as *mut leanh::LeanObject,
            13724376360221892060 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__3_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [108, 99, 85, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__3_value)
                as *mut leanh::LeanObject,
            12623446161643510004 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__6_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [111, 115, 101, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__6_value)
                as *mut leanh::LeanObject,
            6426049140860664012 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__9_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [100, 117, 109, 109, 121, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__9_value)
                as *mut leanh::LeanObject,
            3557712311528643793 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__11_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [85, 110, 105, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__11_value)
                as *mut leanh::LeanObject,
            9833841078580172006 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__14_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [117, 115, 101, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__14_value)
                as *mut leanh::LeanObject,
            10989351250284159100 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__17_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 115, 101, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__18_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__17_value)
                as *mut leanh::LeanObject,
            16233399399348892718 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__20_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [115, 101, 116, 84, 97, 103, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__21_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__20_value)
                as *mut leanh::LeanObject,
            5773271316095278585 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__23_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 110, 99, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__24_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__23_value)
                as *mut leanh::LeanObject,
            3208406958297223247 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__24_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__27_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__26_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__26_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Code_toExprM___closed__28_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__26_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__28_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__28_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__27_value)
                as *mut leanh::LeanObject,
            15761733860085307253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__28_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__30_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__30_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Code_toExprM___closed__31_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__26_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__31_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__31_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__30_value)
                as *mut leanh::LeanObject,
            9255189395584251158 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__31_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__33_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [100, 101, 99, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__34_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__33_value)
                as *mut leanh::LeanObject,
            13886804137793424261 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__34_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__35_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__36_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__36_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__37_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__36_value)
                as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__37_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__38: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__42_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__42: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__42_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__40_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 111, 110, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__40: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__39_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [79, 112, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__39_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Code_toExprM___closed__41_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__39_value)
                as *mut leanh::LeanObject,
            18184376426117065311 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__41_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__41_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__40_value)
                as *mut leanh::LeanObject,
            9480010471355609749 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__41_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__43_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__43: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__45_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 111, 109, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__45: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__45_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Code_toExprM___closed__46_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__39_value)
                as *mut leanh::LeanObject,
            18184376426117065311 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__46_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__46_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__45_value)
                as *mut leanh::LeanObject,
            4893146552088433753 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__46: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__46_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__47_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__47: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__48_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [100, 101, 108, 0],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__48: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__48_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Code_toExprM___closed__49_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__48_value)
                as *mut leanh::LeanObject,
            6947008298398908475 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__49: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_toExprM___closed__49_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__50_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_toExprM___closed__50: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg(
    mut v_t_997_: *mut leanh::LeanObject,
    mut v_k_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_997_) == 0 {
                    v_k_999_ = leanh::lean_ctor_get(v_t_997_, 1);
                    v_v_1000_ = leanh::lean_ctor_get(v_t_997_, 2);
                    v_l_1001_ = leanh::lean_ctor_get(v_t_997_, 3);
                    v_r_1002_ = leanh::lean_ctor_get(v_t_997_, 4);
                    v___x_1003_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_998_, v_k_999_);
                    match v___x_1003_ {
                        0 => {
                            v_t_997_ = v_l_1001_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_1000_);
                            v___x_1005_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1005_, 0, v_v_1000_);
                            return v___x_1005_;
                        }
                        _ => {
                            v_t_997_ = v_r_1002_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1007_ = leanh::lean_box(0);
                    return v___x_1007_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg___boxed(
    mut v_t_1008_: *mut leanh::LeanObject,
    mut v_k_1009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg(v_t_1008_, v_k_1009_);
    leanh::lean_dec(v_k_1009_);
    leanh::lean_dec(v_t_1008_);
    return v_res_1010_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(
    mut v_offset_1011_: *mut leanh::LeanObject,
    mut v_m_1012_: *mut leanh::LeanObject,
    mut v_fvarId_1013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg(v_m_1012_, v_fvarId_1013_);
    if leanh::lean_obj_tag(v___x_1014_) == 0 {
        let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1015_ = l_Lean_Expr_fvar___override(v_fvarId_1013_);
        return v___x_1015_;
    } else {
        let mut v_val_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fvarId_1013_);
        v_val_1016_ = leanh::lean_ctor_get(v___x_1014_, 0);
        leanh::lean_inc(v_val_1016_);
        leanh::lean_dec_ref_known(v___x_1014_, 1);
        v___x_1017_ = lean_nat_sub(v_offset_1011_, v_val_1016_);
        leanh::lean_dec(v_val_1016_);
        v___x_1018_ = leanh::lean_unsigned_to_nat(1);
        v___x_1019_ = lean_nat_sub(v___x_1017_, v___x_1018_);
        leanh::lean_dec(v___x_1017_);
        v___x_1020_ = l_Lean_Expr_bvar___override(v___x_1019_);
        return v___x_1020_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr___boxed(
    mut v_offset_1021_: *mut leanh::LeanObject,
    mut v_m_1022_: *mut leanh::LeanObject,
    mut v_fvarId_1023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1024_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(
        v_offset_1021_,
        v_m_1022_,
        v_fvarId_1023_,
    );
    leanh::lean_dec(v_m_1022_);
    leanh::lean_dec(v_offset_1021_);
    return v_res_1024_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0(
    mut v_00_u03b4_1025_: *mut leanh::LeanObject,
    mut v_t_1026_: *mut leanh::LeanObject,
    mut v_k_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1028_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___redArg(v_t_1026_, v_k_1027_);
    return v___x_1028_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0___boxed(
    mut v_00_u03b4_1029_: *mut leanh::LeanObject,
    mut v_t_1030_: *mut leanh::LeanObject,
    mut v_k_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1032_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr_spec__0(v_00_u03b4_1029_, v_t_1030_, v_k_1031_);
    leanh::lean_dec(v_k_1031_);
    leanh::lean_dec(v_t_1030_);
    return v_res_1032_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
    mut v_m_1033_: *mut leanh::LeanObject,
    mut v_o_1034_: *mut leanh::LeanObject,
    mut v_e_1035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_e_1035_) {
        1 => {
            let mut v_fvarId_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_1036_ = leanh::lean_ctor_get(v_e_1035_, 0);
            leanh::lean_inc(v_fvarId_1036_);
            leanh::lean_dec_ref_known(v_e_1035_, 1);
            v___x_1037_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(
                v_o_1034_,
                v_m_1033_,
                v_fvarId_1036_,
            );
            return v___x_1037_;
        }
        5 => {
            let mut v_fn_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_arg_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_fn_1038_ = leanh::lean_ctor_get(v_e_1035_, 0);
            leanh::lean_inc_ref(v_fn_1038_);
            v_arg_1039_ = leanh::lean_ctor_get(v_e_1035_, 1);
            leanh::lean_inc_ref(v_arg_1039_);
            leanh::lean_dec_ref_known(v_e_1035_, 2);
            v___x_1040_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_, v_o_1034_, v_fn_1038_,
            );
            v___x_1041_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v_o_1034_,
                v_arg_1039_,
            );
            v___x_1042_ = l_Lean_Expr_app___override(v___x_1040_, v___x_1041_);
            return v___x_1042_;
        }
        6 => {
            let mut v_binderName_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderType_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1046_: u8 = 0;
            let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_binderName_1043_ = leanh::lean_ctor_get(v_e_1035_, 0);
            leanh::lean_inc(v_binderName_1043_);
            v_binderType_1044_ = leanh::lean_ctor_get(v_e_1035_, 1);
            leanh::lean_inc_ref(v_binderType_1044_);
            v_body_1045_ = leanh::lean_ctor_get(v_e_1035_, 2);
            leanh::lean_inc_ref(v_body_1045_);
            v_binderInfo_1046_ = leanh::lean_ctor_get_uint8(
                v_e_1035_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            leanh::lean_dec_ref_known(v_e_1035_, 3);
            v___x_1047_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v_o_1034_,
                v_binderType_1044_,
            );
            v___x_1048_ = leanh::lean_unsigned_to_nat(1);
            v___x_1049_ = lean_nat_add(v_o_1034_, v___x_1048_);
            v___x_1050_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v___x_1049_,
                v_body_1045_,
            );
            leanh::lean_dec(v___x_1049_);
            v___x_1051_ = l_Lean_Expr_lam___override(
                v_binderName_1043_,
                v___x_1047_,
                v___x_1050_,
                v_binderInfo_1046_,
            );
            return v___x_1051_;
        }
        7 => {
            let mut v_binderName_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderType_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_1055_: u8 = 0;
            let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_binderName_1052_ = leanh::lean_ctor_get(v_e_1035_, 0);
            leanh::lean_inc(v_binderName_1052_);
            v_binderType_1053_ = leanh::lean_ctor_get(v_e_1035_, 1);
            leanh::lean_inc_ref(v_binderType_1053_);
            v_body_1054_ = leanh::lean_ctor_get(v_e_1035_, 2);
            leanh::lean_inc_ref(v_body_1054_);
            v_binderInfo_1055_ = leanh::lean_ctor_get_uint8(
                v_e_1035_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            leanh::lean_dec_ref_known(v_e_1035_, 3);
            v___x_1056_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v_o_1034_,
                v_binderType_1053_,
            );
            v___x_1057_ = leanh::lean_unsigned_to_nat(1);
            v___x_1058_ = lean_nat_add(v_o_1034_, v___x_1057_);
            v___x_1059_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v___x_1058_,
                v_body_1054_,
            );
            leanh::lean_dec(v___x_1058_);
            v___x_1060_ = l_Lean_Expr_forallE___override(
                v_binderName_1052_,
                v___x_1056_,
                v___x_1059_,
                v_binderInfo_1055_,
            );
            return v___x_1060_;
        }
        8 => {
            let mut v_declName_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_nondep_1065_: u8 = 0;
            let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_declName_1061_ = leanh::lean_ctor_get(v_e_1035_, 0);
            leanh::lean_inc(v_declName_1061_);
            v_type_1062_ = leanh::lean_ctor_get(v_e_1035_, 1);
            leanh::lean_inc_ref(v_type_1062_);
            v_value_1063_ = leanh::lean_ctor_get(v_e_1035_, 2);
            leanh::lean_inc_ref(v_value_1063_);
            v_body_1064_ = leanh::lean_ctor_get(v_e_1035_, 3);
            leanh::lean_inc_ref(v_body_1064_);
            v_nondep_1065_ = leanh::lean_ctor_get_uint8(
                v_e_1035_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
            );
            leanh::lean_dec_ref_known(v_e_1035_, 4);
            v___x_1066_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v_o_1034_,
                v_type_1062_,
            );
            v___x_1067_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v_o_1034_,
                v_value_1063_,
            );
            v___x_1068_ = leanh::lean_unsigned_to_nat(1);
            v___x_1069_ = lean_nat_add(v_o_1034_, v___x_1068_);
            v___x_1070_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v___x_1069_,
                v_body_1064_,
            );
            leanh::lean_dec(v___x_1069_);
            v___x_1071_ = l_Lean_Expr_letE___override(
                v_declName_1061_,
                v___x_1066_,
                v___x_1067_,
                v___x_1070_,
                v_nondep_1065_,
            );
            return v___x_1071_;
        }
        10 => {
            let mut v_data_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_data_1072_ = leanh::lean_ctor_get(v_e_1035_, 0);
            leanh::lean_inc(v_data_1072_);
            v_expr_1073_ = leanh::lean_ctor_get(v_e_1035_, 1);
            leanh::lean_inc_ref(v_expr_1073_);
            leanh::lean_dec_ref_known(v_e_1035_, 2);
            v___x_1074_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v_o_1034_,
                v_expr_1073_,
            );
            v___x_1075_ = l_Lean_Expr_mdata___override(v_data_1072_, v___x_1074_);
            return v___x_1075_;
        }
        11 => {
            let mut v_typeName_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_struct_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_typeName_1076_ = leanh::lean_ctor_get(v_e_1035_, 0);
            leanh::lean_inc(v_typeName_1076_);
            v_idx_1077_ = leanh::lean_ctor_get(v_e_1035_, 1);
            leanh::lean_inc(v_idx_1077_);
            v_struct_1078_ = leanh::lean_ctor_get(v_e_1035_, 2);
            leanh::lean_inc_ref(v_struct_1078_);
            leanh::lean_dec_ref_known(v_e_1035_, 3);
            v___x_1079_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                v_m_1033_,
                v_o_1034_,
                v_struct_1078_,
            );
            v___x_1080_ = l_Lean_Expr_proj___override(v_typeName_1076_, v_idx_1077_, v___x_1079_);
            return v___x_1080_;
        }
        _ => {
            return v_e_1035_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go___boxed(
    mut v_m_1081_: *mut leanh::LeanObject,
    mut v_o_1082_: *mut leanh::LeanObject,
    mut v_e_1083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
        v_m_1081_, v_o_1082_, v_e_1083_,
    );
    leanh::lean_dec(v_o_1082_);
    leanh::lean_dec(v_m_1081_);
    return v_res_1084_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27(
    mut v_offset_1085_: *mut leanh::LeanObject,
    mut v_m_1086_: *mut leanh::LeanObject,
    mut v_e_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1088_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
        v_m_1086_,
        v_offset_1085_,
        v_e_1087_,
    );
    return v___x_1088_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27___boxed(
    mut v_offset_1089_: *mut leanh::LeanObject,
    mut v_m_1090_: *mut leanh::LeanObject,
    mut v_e_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27(
        v_offset_1089_,
        v_m_1090_,
        v_e_1091_,
    );
    leanh::lean_dec(v_m_1090_);
    leanh::lean_dec(v_offset_1089_);
    return v_res_1092_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(
    mut v_pu_1093_: u8,
    mut v_params_1094_: *mut leanh::LeanObject,
    mut v_offset_1095_: *mut leanh::LeanObject,
    mut v_m_1096_: *mut leanh::LeanObject,
    mut v_i_1097_: *mut leanh::LeanObject,
    mut v_e_1098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: u8 = 0;
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_param_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_domain_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u8 = 0;
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1099_ = leanh::lean_unsigned_to_nat(0);
                v___x_1100_ = lean_nat_dec_lt(v___x_1099_, v_i_1097_);
                if v___x_1100_ == 0 {
                    leanh::lean_dec(v_i_1097_);
                    leanh::lean_dec(v_offset_1095_);
                    return v_e_1098_;
                } else {
                    v___x_1101_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v_pu_1093_);
                    v___x_1102_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1103_ = lean_nat_sub(v_i_1097_, v___x_1102_);
                    leanh::lean_dec(v_i_1097_);
                    v_param_1104_ = lean_array_get(v___x_1101_, v_params_1094_, v___x_1103_);
                    leanh::lean_dec_ref(v___x_1101_);
                    v_binderName_1105_ = leanh::lean_ctor_get(v_param_1104_, 1);
                    leanh::lean_inc(v_binderName_1105_);
                    v_type_1106_ = leanh::lean_ctor_get(v_param_1104_, 2);
                    leanh::lean_inc_ref(v_type_1106_);
                    leanh::lean_dec(v_param_1104_);
                    v___x_1107_ = lean_nat_sub(v_offset_1095_, v___x_1102_);
                    leanh::lean_dec(v_offset_1095_);
                    v_domain_1108_ =
                        l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                            v_m_1096_,
                            v___x_1107_,
                            v_type_1106_,
                        );
                    v___x_1109_ = 0;
                    v___x_1110_ = l_Lean_Expr_lam___override(
                        v_binderName_1105_,
                        v_domain_1108_,
                        v_e_1098_,
                        v___x_1109_,
                    );
                    v_offset_1095_ = v___x_1107_;
                    v_i_1097_ = v___x_1103_;
                    v_e_1098_ = v___x_1110_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go___boxed(
    mut v_pu_1112_: *mut leanh::LeanObject,
    mut v_params_1113_: *mut leanh::LeanObject,
    mut v_offset_1114_: *mut leanh::LeanObject,
    mut v_m_1115_: *mut leanh::LeanObject,
    mut v_i_1116_: *mut leanh::LeanObject,
    mut v_e_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1118_: u8 = 0;
    let mut v_res_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1118_ = (leanh::lean_unbox(v_pu_1112_) as u8);
    v_res_1119_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(
        v_pu_boxed_1118_,
        v_params_1113_,
        v_offset_1114_,
        v_m_1115_,
        v_i_1116_,
        v_e_1117_,
    );
    leanh::lean_dec(v_m_1115_);
    leanh::lean_dec_ref(v_params_1113_);
    return v_res_1119_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(
    mut v_pu_1120_: u8,
    mut v_params_1121_: *mut leanh::LeanObject,
    mut v_e_1122_: *mut leanh::LeanObject,
    mut v_a_1123_: *mut leanh::LeanObject,
    mut v_a_1124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1125_ = lean_array_get_size(v_params_1121_);
    leanh::lean_inc(v_a_1123_);
    v___x_1126_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(
        v_pu_1120_,
        v_params_1121_,
        v_a_1123_,
        v_a_1124_,
        v___x_1125_,
        v_e_1122_,
    );
    v___x_1127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    leanh::lean_ctor_set(v___x_1127_, 1, v_a_1124_);
    return v___x_1127_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___boxed(
    mut v_pu_1128_: *mut leanh::LeanObject,
    mut v_params_1129_: *mut leanh::LeanObject,
    mut v_e_1130_: *mut leanh::LeanObject,
    mut v_a_1131_: *mut leanh::LeanObject,
    mut v_a_1132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1133_: u8 = 0;
    let mut v_res_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1133_ = (leanh::lean_unbox(v_pu_1128_) as u8);
    v_res_1134_ = l_Lean_Compiler_LCNF_ToExpr_mkLambdaM(
        v_pu_boxed_1133_,
        v_params_1129_,
        v_e_1130_,
        v_a_1131_,
        v_a_1132_,
    );
    leanh::lean_dec(v_a_1131_);
    leanh::lean_dec_ref(v_params_1129_);
    return v_res_1134_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(
    mut v_fvarId_1135_: *mut leanh::LeanObject,
    mut v_a_1136_: *mut leanh::LeanObject,
    mut v_a_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1138_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(
        v_a_1136_,
        v_a_1137_,
        v_fvarId_1135_,
    );
    v___x_1139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1139_, 0, v___x_1138_);
    leanh::lean_ctor_set(v___x_1139_, 1, v_a_1137_);
    return v___x_1139_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM___boxed(
    mut v_fvarId_1140_: *mut leanh::LeanObject,
    mut v_a_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1143_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExprM(
        v_fvarId_1140_,
        v_a_1141_,
        v_a_1142_,
    );
    leanh::lean_dec(v_a_1141_);
    return v_res_1143_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_abstractM(
    mut v_e_1144_: *mut leanh::LeanObject,
    mut v_a_1145_: *mut leanh::LeanObject,
    mut v_a_1146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1147_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
        v_a_1146_, v_a_1145_, v_e_1144_,
    );
    v___x_1148_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1148_, 0, v___x_1147_);
    leanh::lean_ctor_set(v___x_1148_, 1, v_a_1146_);
    return v___x_1148_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_abstractM___boxed(
    mut v_e_1149_: *mut leanh::LeanObject,
    mut v_a_1150_: *mut leanh::LeanObject,
    mut v_a_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1152_ = l_Lean_Compiler_LCNF_ToExpr_abstractM(v_e_1149_, v_a_1150_, v_a_1151_);
    leanh::lean_dec(v_a_1150_);
    return v_res_1152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(
    mut v_fvarId_1153_: *mut leanh::LeanObject,
    mut v_k_1154_: *mut leanh::LeanObject,
    mut v_a_1155_: *mut leanh::LeanObject,
    mut v_a_1156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1155_);
    v___x_1157_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1153_, v_a_1155_, v_a_1156_);
    v___x_1158_ = leanh::lean_unsigned_to_nat(1);
    v___x_1159_ = lean_nat_add(v_a_1155_, v___x_1158_);
    v___x_1160_ = leanh::lean_apply_2(v_k_1154_, v___x_1159_, v___x_1157_);
    return v___x_1160_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg___boxed(
    mut v_fvarId_1161_: *mut leanh::LeanObject,
    mut v_k_1162_: *mut leanh::LeanObject,
    mut v_a_1163_: *mut leanh::LeanObject,
    mut v_a_1164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ = l_Lean_Compiler_LCNF_ToExpr_withFVar___redArg(
        v_fvarId_1161_,
        v_k_1162_,
        v_a_1163_,
        v_a_1164_,
    );
    leanh::lean_dec(v_a_1163_);
    return v_res_1165_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_withFVar(
    mut v_00_u03b1_1166_: *mut leanh::LeanObject,
    mut v_fvarId_1167_: *mut leanh::LeanObject,
    mut v_k_1168_: *mut leanh::LeanObject,
    mut v_a_1169_: *mut leanh::LeanObject,
    mut v_a_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1169_);
    v___x_1171_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1167_, v_a_1169_, v_a_1170_);
    v___x_1172_ = leanh::lean_unsigned_to_nat(1);
    v___x_1173_ = lean_nat_add(v_a_1169_, v___x_1172_);
    v___x_1174_ = leanh::lean_apply_2(v_k_1168_, v___x_1173_, v___x_1171_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_withFVar___boxed(
    mut v_00_u03b1_1175_: *mut leanh::LeanObject,
    mut v_fvarId_1176_: *mut leanh::LeanObject,
    mut v_k_1177_: *mut leanh::LeanObject,
    mut v_a_1178_: *mut leanh::LeanObject,
    mut v_a_1179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1180_ = l_Lean_Compiler_LCNF_ToExpr_withFVar(
        v_00_u03b1_1175_,
        v_fvarId_1176_,
        v_k_1177_,
        v_a_1178_,
        v_a_1179_,
    );
    leanh::lean_dec(v_a_1178_);
    return v_res_1180_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(
    mut v_params_1181_: *mut leanh::LeanObject,
    mut v_k_1182_: *mut leanh::LeanObject,
    mut v_i_1183_: *mut leanh::LeanObject,
    mut v_a_1184_: *mut leanh::LeanObject,
    mut v_a_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1186_ = lean_array_get_size(v_params_1181_);
                v___x_1187_ = lean_nat_dec_lt(v_i_1183_, v___x_1186_);
                if v___x_1187_ == 0 {
                    leanh::lean_dec(v_i_1183_);
                    v___x_1188_ = leanh::lean_apply_2(v_k_1182_, v_a_1184_, v_a_1185_);
                    return v___x_1188_;
                } else {
                    v___x_1189_ = lean_array_fget_borrowed(v_params_1181_, v_i_1183_);
                    v_fvarId_1190_ = leanh::lean_ctor_get(v___x_1189_, 0);
                    v___x_1191_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1192_ = lean_nat_add(v_i_1183_, v___x_1191_);
                    leanh::lean_dec(v_i_1183_);
                    leanh::lean_inc(v_a_1184_);
                    leanh::lean_inc(v_fvarId_1190_);
                    v___x_1193_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1190_, v_a_1184_, v_a_1185_);
                    v___x_1194_ = lean_nat_add(v_a_1184_, v___x_1191_);
                    leanh::lean_dec(v_a_1184_);
                    v_i_1183_ = v___x_1192_;
                    v_a_1184_ = v___x_1194_;
                    v_a_1185_ = v___x_1193_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg___boxed(
    mut v_params_1196_: *mut leanh::LeanObject,
    mut v_k_1197_: *mut leanh::LeanObject,
    mut v_i_1198_: *mut leanh::LeanObject,
    mut v_a_1199_: *mut leanh::LeanObject,
    mut v_a_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ =
        l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(
            v_params_1196_,
            v_k_1197_,
            v_i_1198_,
            v_a_1199_,
            v_a_1200_,
        );
    leanh::lean_dec_ref(v_params_1196_);
    return v_res_1201_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(
    mut v_pu_1202_: u8,
    mut v_00_u03b1_1203_: *mut leanh::LeanObject,
    mut v_params_1204_: *mut leanh::LeanObject,
    mut v_k_1205_: *mut leanh::LeanObject,
    mut v_i_1206_: *mut leanh::LeanObject,
    mut v_a_1207_: *mut leanh::LeanObject,
    mut v_a_1208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1207_);
    v___x_1209_ =
        l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(
            v_params_1204_,
            v_k_1205_,
            v_i_1206_,
            v_a_1207_,
            v_a_1208_,
        );
    return v___x_1209_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___boxed(
    mut v_pu_1210_: *mut leanh::LeanObject,
    mut v_00_u03b1_1211_: *mut leanh::LeanObject,
    mut v_params_1212_: *mut leanh::LeanObject,
    mut v_k_1213_: *mut leanh::LeanObject,
    mut v_i_1214_: *mut leanh::LeanObject,
    mut v_a_1215_: *mut leanh::LeanObject,
    mut v_a_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1217_: u8 = 0;
    let mut v_res_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1217_ = (leanh::lean_unbox(v_pu_1210_) as u8);
    v_res_1218_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go(
        v_pu_boxed_1217_,
        v_00_u03b1_1211_,
        v_params_1212_,
        v_k_1213_,
        v_i_1214_,
        v_a_1215_,
        v_a_1216_,
    );
    leanh::lean_dec(v_a_1215_);
    leanh::lean_dec_ref(v_params_1212_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(
    mut v_params_1219_: *mut leanh::LeanObject,
    mut v_k_1220_: *mut leanh::LeanObject,
    mut v_a_1221_: *mut leanh::LeanObject,
    mut v_a_1222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1223_ = leanh::lean_unsigned_to_nat(0);
    leanh::lean_inc(v_a_1221_);
    v___x_1224_ =
        l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(
            v_params_1219_,
            v_k_1220_,
            v___x_1223_,
            v_a_1221_,
            v_a_1222_,
        );
    return v___x_1224_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_withParams___redArg___boxed(
    mut v_params_1225_: *mut leanh::LeanObject,
    mut v_k_1226_: *mut leanh::LeanObject,
    mut v_a_1227_: *mut leanh::LeanObject,
    mut v_a_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Lean_Compiler_LCNF_ToExpr_withParams___redArg(
        v_params_1225_,
        v_k_1226_,
        v_a_1227_,
        v_a_1228_,
    );
    leanh::lean_dec(v_a_1227_);
    leanh::lean_dec_ref(v_params_1225_);
    return v_res_1229_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_withParams(
    mut v_pu_1230_: u8,
    mut v_00_u03b1_1231_: *mut leanh::LeanObject,
    mut v_params_1232_: *mut leanh::LeanObject,
    mut v_k_1233_: *mut leanh::LeanObject,
    mut v_a_1234_: *mut leanh::LeanObject,
    mut v_a_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = leanh::lean_unsigned_to_nat(0);
    leanh::lean_inc(v_a_1234_);
    v___x_1237_ =
        l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___redArg(
            v_params_1232_,
            v_k_1233_,
            v___x_1236_,
            v_a_1234_,
            v_a_1235_,
        );
    return v___x_1237_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_withParams___boxed(
    mut v_pu_1238_: *mut leanh::LeanObject,
    mut v_00_u03b1_1239_: *mut leanh::LeanObject,
    mut v_params_1240_: *mut leanh::LeanObject,
    mut v_k_1241_: *mut leanh::LeanObject,
    mut v_a_1242_: *mut leanh::LeanObject,
    mut v_a_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1244_: u8 = 0;
    let mut v_res_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1244_ = (leanh::lean_unbox(v_pu_1238_) as u8);
    v_res_1245_ = l_Lean_Compiler_LCNF_ToExpr_withParams(
        v_pu_boxed_1244_,
        v_00_u03b1_1239_,
        v_params_1240_,
        v_k_1241_,
        v_a_1242_,
        v_a_1243_,
    );
    leanh::lean_dec(v_a_1242_);
    leanh::lean_dec_ref(v_params_1240_);
    return v_res_1245_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_run___redArg(
    mut v_x_1246_: *mut leanh::LeanObject,
    mut v_offset_1247_: *mut leanh::LeanObject,
    mut v_levelMap_1248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = leanh::lean_apply_2(v_x_1246_, v_offset_1247_, v_levelMap_1248_);
    v_fst_1250_ = leanh::lean_ctor_get(v___x_1249_, 0);
    leanh::lean_inc(v_fst_1250_);
    leanh::lean_dec_ref(v___x_1249_);
    return v_fst_1250_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_run(
    mut v_00_u03b1_1251_: *mut leanh::LeanObject,
    mut v_x_1252_: *mut leanh::LeanObject,
    mut v_offset_1253_: *mut leanh::LeanObject,
    mut v_levelMap_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = leanh::lean_apply_2(v_x_1252_, v_offset_1253_, v_levelMap_1254_);
    v_fst_1256_ = leanh::lean_ctor_get(v___x_1255_, 0);
    leanh::lean_inc(v_fst_1256_);
    leanh::lean_dec_ref(v___x_1255_);
    return v_fst_1256_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___lam__0(
    mut v_x1_1257_: *mut leanh::LeanObject,
    mut v_x2_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x1_1257_) == 0 {
        let mut v_size_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_size_1259_ = leanh::lean_ctor_get(v_x1_1257_, 0);
        leanh::lean_inc(v_size_1259_);
        v___x_1260_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_x2_1258_, v_size_1259_, v_x1_1257_);
        return v___x_1260_;
    } else {
        let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1261_ = leanh::lean_unsigned_to_nat(0);
        v___x_1262_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_x2_1258_, v___x_1261_, v_x1_1257_);
        return v___x_1262_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg(
    mut v_x_1283_: *mut leanh::LeanObject,
    mut v_xs_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u8 = 0;
    let mut v___f_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: usize = 0;
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: usize = 0;
    let mut v___x_1300_: usize = 0;
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1285_ = leanh::lean_box(1);
                v___x_1286_ = leanh::lean_unsigned_to_nat(0);
                v___x_1287_ = lean_array_get_size(v_xs_1284_);
                v___x_1292_ = l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9;
                v___x_1293_ = lean_nat_dec_lt(v___x_1286_, v___x_1287_);
                if v___x_1293_ == 0 {
                    leanh::lean_dec_ref(v_xs_1284_);
                    v___y_1289_ = v___x_1285_;
                    state = 1;
                    continue;
                } else {
                    v___f_1294_ = l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10;
                    v___x_1295_ = lean_nat_dec_le(v___x_1287_, v___x_1287_);
                    if v___x_1295_ == 0 {
                        if v___x_1293_ == 0 {
                            leanh::lean_dec_ref(v_xs_1284_);
                            v___y_1289_ = v___x_1285_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1296_ = 0usize;
                            v___x_1297_ = lean_usize_of_nat(v___x_1287_);
                            v___x_1298_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_1292_,
                                    v___f_1294_,
                                    v_xs_1284_,
                                    v___x_1296_,
                                    v___x_1297_,
                                    v___x_1285_,
                                );
                            v___y_1289_ = v___x_1298_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1299_ = 0usize;
                        v___x_1300_ = lean_usize_of_nat(v___x_1287_);
                        v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1292_,
                            v___f_1294_,
                            v_xs_1284_,
                            v___x_1299_,
                            v___x_1300_,
                            v___x_1285_,
                        );
                        v___y_1289_ = v___x_1301_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1290_ = leanh::lean_apply_2(v_x_1283_, v___x_1287_, v___y_1289_);
                v_fst_1291_ = leanh::lean_ctor_get(v___x_1290_, 0);
                leanh::lean_inc(v_fst_1291_);
                leanh::lean_dec_ref(v___x_1290_);
                return v_fst_1291_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ToExpr_run_x27(
    mut v_00_u03b1_1302_: *mut leanh::LeanObject,
    mut v_x_1303_: *mut leanh::LeanObject,
    mut v_xs_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: u8 = 0;
    let mut v___f_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1316_: usize = 0;
    let mut v___x_1317_: usize = 0;
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: usize = 0;
    let mut v___x_1320_: usize = 0;
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1305_ = leanh::lean_box(1);
                v___x_1306_ = leanh::lean_unsigned_to_nat(0);
                v___x_1307_ = lean_array_get_size(v_xs_1304_);
                v___x_1312_ = l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__9;
                v___x_1313_ = lean_nat_dec_lt(v___x_1306_, v___x_1307_);
                if v___x_1313_ == 0 {
                    leanh::lean_dec_ref(v_xs_1304_);
                    v___y_1309_ = v___x_1305_;
                    state = 1;
                    continue;
                } else {
                    v___f_1314_ = l_Lean_Compiler_LCNF_ToExpr_run_x27___redArg___closed__10;
                    v___x_1315_ = lean_nat_dec_le(v___x_1307_, v___x_1307_);
                    if v___x_1315_ == 0 {
                        if v___x_1313_ == 0 {
                            leanh::lean_dec_ref(v_xs_1304_);
                            v___y_1309_ = v___x_1305_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1316_ = 0usize;
                            v___x_1317_ = lean_usize_of_nat(v___x_1307_);
                            v___x_1318_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_1312_,
                                    v___f_1314_,
                                    v_xs_1304_,
                                    v___x_1316_,
                                    v___x_1317_,
                                    v___x_1305_,
                                );
                            v___y_1309_ = v___x_1318_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1319_ = 0usize;
                        v___x_1320_ = lean_usize_of_nat(v___x_1307_);
                        v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1312_,
                            v___f_1314_,
                            v_xs_1304_,
                            v___x_1319_,
                            v___x_1320_,
                            v___x_1305_,
                        );
                        v___y_1309_ = v___x_1321_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1310_ = leanh::lean_apply_2(v_x_1303_, v___x_1307_, v___y_1309_);
                v_fst_1311_ = leanh::lean_ctor_get(v___x_1310_, 0);
                leanh::lean_inc(v_fst_1311_);
                leanh::lean_dec_ref(v___x_1310_);
                return v_fst_1311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(
    mut v_arg_1322_: *mut leanh::LeanObject,
    mut v_a_1323_: *mut leanh::LeanObject,
    mut v_a_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v_arg_1322_);
    v___x_1326_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
        v_a_1324_,
        v_a_1323_,
        v___x_1325_,
    );
    v___x_1327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1327_, 0, v___x_1326_);
    leanh::lean_ctor_set(v___x_1327_, 1, v_a_1324_);
    return v___x_1327_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg___boxed(
    mut v_arg_1328_: *mut leanh::LeanObject,
    mut v_a_1329_: *mut leanh::LeanObject,
    mut v_a_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(
        v_arg_1328_,
        v_a_1329_,
        v_a_1330_,
    );
    leanh::lean_dec(v_a_1329_);
    return v_res_1331_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(
    mut v_pu_1332_: u8,
    mut v_arg_1333_: *mut leanh::LeanObject,
    mut v_a_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1336_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(
        v_arg_1333_,
        v_a_1334_,
        v_a_1335_,
    );
    return v___x_1336_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___boxed(
    mut v_pu_1337_: *mut leanh::LeanObject,
    mut v_arg_1338_: *mut leanh::LeanObject,
    mut v_a_1339_: *mut leanh::LeanObject,
    mut v_a_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1341_: u8 = 0;
    let mut v_res_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1341_ = (leanh::lean_unbox(v_pu_1337_) as u8);
    v_res_1342_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM(
        v_pu_boxed_1341_,
        v_arg_1338_,
        v_a_1339_,
        v_a_1340_,
    );
    leanh::lean_dec(v_a_1339_);
    return v_res_1342_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(
    mut v_sz_1343_: usize,
    mut v_i_1344_: usize,
    mut v_bs_1345_: *mut leanh::LeanObject,
    mut v___y_1346_: *mut leanh::LeanObject,
    mut v___y_1347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1348_: u8 = 0;
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: usize = 0;
    let mut v___x_1357_: usize = 0;
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1348_ = lean_usize_dec_lt(v_i_1344_, v_sz_1343_);
                if v___x_1348_ == 0 {
                    v___x_1349_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1349_, 0, v_bs_1345_);
                    leanh::lean_ctor_set(v___x_1349_, 1, v___y_1347_);
                    return v___x_1349_;
                } else {
                    v_v_1350_ = lean_array_uget_borrowed(v_bs_1345_, v_i_1344_);
                    leanh::lean_inc(v_v_1350_);
                    v___x_1351_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_v_1350_, v___y_1346_, v___y_1347_);
                    v_fst_1352_ = leanh::lean_ctor_get(v___x_1351_, 0);
                    leanh::lean_inc(v_fst_1352_);
                    v_snd_1353_ = leanh::lean_ctor_get(v___x_1351_, 1);
                    leanh::lean_inc(v_snd_1353_);
                    leanh::lean_dec_ref(v___x_1351_);
                    v___x_1354_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1355_ = lean_array_uset(v_bs_1345_, v_i_1344_, v___x_1354_);
                    v___x_1356_ = 1usize;
                    v___x_1357_ = lean_usize_add(v_i_1344_, v___x_1356_);
                    v___x_1358_ = lean_array_uset(v_bs_x27_1355_, v_i_1344_, v_fst_1352_);
                    v_i_1344_ = v___x_1357_;
                    v_bs_1345_ = v___x_1358_;
                    v___y_1347_ = v_snd_1353_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg___boxed(
    mut v_sz_1360_: *mut leanh::LeanObject,
    mut v_i_1361_: *mut leanh::LeanObject,
    mut v_bs_1362_: *mut leanh::LeanObject,
    mut v___y_1363_: *mut leanh::LeanObject,
    mut v___y_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1365_: usize = 0;
    let mut v_i_boxed_1366_: usize = 0;
    let mut v_res_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1365_ = leanh::lean_unbox_usize(v_sz_1360_);
    leanh::lean_dec(v_sz_1360_);
    v_i_boxed_1366_ = leanh::lean_unbox_usize(v_i_1361_);
    leanh::lean_dec(v_i_1361_);
    v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_boxed_1365_, v_i_boxed_1366_, v_bs_1362_, v___y_1363_, v___y_1364_);
    leanh::lean_dec(v___y_1363_);
    return v_res_1367_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(
    mut v_pu_1368_: u8,
    mut v_sz_1369_: usize,
    mut v_i_1370_: usize,
    mut v_bs_1371_: *mut leanh::LeanObject,
    mut v___y_1372_: *mut leanh::LeanObject,
    mut v___y_1373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: usize = 0;
    let mut v___x_1383_: usize = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1374_ = lean_usize_dec_lt(v_i_1370_, v_sz_1369_);
                if v___x_1374_ == 0 {
                    v___x_1375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1375_, 0, v_bs_1371_);
                    leanh::lean_ctor_set(v___x_1375_, 1, v___y_1373_);
                    return v___x_1375_;
                } else {
                    v_v_1376_ = lean_array_uget(v_bs_1371_, v_i_1370_);
                    v___x_1377_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1378_ = lean_array_uset(v_bs_1371_, v_i_1370_, v___x_1377_);
                    match leanh::lean_obj_tag(v_v_1376_) {
                        0 => {
                            v_ctorName_1386_ = leanh::lean_ctor_get(v_v_1376_, 0);
                            leanh::lean_inc(v_ctorName_1386_);
                            v_params_1387_ = leanh::lean_ctor_get(v_v_1376_, 1);
                            leanh::lean_inc_ref(v_params_1387_);
                            v_code_1388_ = leanh::lean_ctor_get(v_v_1376_, 2);
                            leanh::lean_inc_ref(v_code_1388_);
                            leanh::lean_dec_ref_known(v_v_1376_, 3);
                            leanh::lean_inc(v___y_1372_);
                            v___x_1389_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_1368_, v_code_1388_, v_params_1387_, v_params_1387_, v___x_1377_, v___y_1372_, v___y_1373_);
                            leanh::lean_dec_ref(v_params_1387_);
                            v_fst_1390_ = leanh::lean_ctor_get(v___x_1389_, 0);
                            leanh::lean_inc(v_fst_1390_);
                            v_snd_1391_ = leanh::lean_ctor_get(v___x_1389_, 1);
                            leanh::lean_inc(v_snd_1391_);
                            leanh::lean_dec_ref(v___x_1389_);
                            v___x_1392_ = leanh::lean_box(0);
                            v___x_1393_ = l_Lean_mkConst(v_ctorName_1386_, v___x_1392_);
                            v___x_1394_ = l_Lean_Expr_app___override(v___x_1393_, v_fst_1390_);
                            v_fst_1380_ = v___x_1394_;
                            v_snd_1381_ = v_snd_1391_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_info_1395_ = leanh::lean_ctor_get(v_v_1376_, 0);
                            leanh::lean_inc_ref(v_info_1395_);
                            v_code_1396_ = leanh::lean_ctor_get(v_v_1376_, 1);
                            leanh::lean_inc_ref(v_code_1396_);
                            leanh::lean_dec_ref_known(v_v_1376_, 2);
                            v___x_1397_ = l_Lean_Compiler_LCNF_Code_toExprM(
                                v_pu_1368_,
                                v_code_1396_,
                                v___y_1372_,
                                v___y_1373_,
                            );
                            v_fst_1398_ = leanh::lean_ctor_get(v___x_1397_, 0);
                            leanh::lean_inc(v_fst_1398_);
                            v_snd_1399_ = leanh::lean_ctor_get(v___x_1397_, 1);
                            leanh::lean_inc(v_snd_1399_);
                            leanh::lean_dec_ref(v___x_1397_);
                            v_name_1400_ = leanh::lean_ctor_get(v_info_1395_, 0);
                            leanh::lean_inc(v_name_1400_);
                            leanh::lean_dec_ref(v_info_1395_);
                            v___x_1401_ = leanh::lean_box(0);
                            v___x_1402_ = l_Lean_mkConst(v_name_1400_, v___x_1401_);
                            v___x_1403_ = l_Lean_Expr_app___override(v___x_1402_, v_fst_1398_);
                            v_fst_1380_ = v___x_1403_;
                            v_snd_1381_ = v_snd_1399_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1404_ = leanh::lean_ctor_get(v_v_1376_, 0);
                            leanh::lean_inc_ref(v_code_1404_);
                            leanh::lean_dec_ref_known(v_v_1376_, 1);
                            v___x_1405_ = l_Lean_Compiler_LCNF_Code_toExprM(
                                v_pu_1368_,
                                v_code_1404_,
                                v___y_1372_,
                                v___y_1373_,
                            );
                            v_fst_1406_ = leanh::lean_ctor_get(v___x_1405_, 0);
                            leanh::lean_inc(v_fst_1406_);
                            v_snd_1407_ = leanh::lean_ctor_get(v___x_1405_, 1);
                            leanh::lean_inc(v_snd_1407_);
                            leanh::lean_dec_ref(v___x_1405_);
                            v_fst_1380_ = v_fst_1406_;
                            v_snd_1381_ = v_snd_1407_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1382_ = 1usize;
                v___x_1383_ = lean_usize_add(v_i_1370_, v___x_1382_);
                v___x_1384_ = lean_array_uset(v_bs_x27_1378_, v_i_1370_, v_fst_1380_);
                v_i_1370_ = v___x_1383_;
                v_bs_1371_ = v___x_1384_;
                v___y_1373_ = v_snd_1381_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ = leanh::lean_box(0);
    v___x_1412_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__1;
    v___x_1413_ = l_Lean_mkConst(v___x_1412_, v___x_1411_);
    return v___x_1413_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = leanh::lean_box(0);
    v___x_1418_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__4;
    v___x_1419_ = l_Lean_mkConst(v___x_1418_, v___x_1417_);
    return v___x_1419_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1423_ = leanh::lean_box(0);
    v___x_1424_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__7;
    v___x_1425_ = l_Lean_mkConst(v___x_1424_, v___x_1423_);
    return v___x_1425_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13() -> *mut leanh::LeanObject
{
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = leanh::lean_box(0);
    v___x_1433_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__12;
    v___x_1434_ = l_Lean_mkConst(v___x_1433_, v___x_1432_);
    return v___x_1434_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16() -> *mut leanh::LeanObject
{
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = leanh::lean_box(0);
    v___x_1439_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__15;
    v___x_1440_ = l_Lean_mkConst(v___x_1439_, v___x_1438_);
    return v___x_1440_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19() -> *mut leanh::LeanObject
{
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1444_ = leanh::lean_box(0);
    v___x_1445_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__18;
    v___x_1446_ = l_Lean_mkConst(v___x_1445_, v___x_1444_);
    return v___x_1446_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22() -> *mut leanh::LeanObject
{
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = leanh::lean_box(0);
    v___x_1451_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__21;
    v___x_1452_ = l_Lean_mkConst(v___x_1451_, v___x_1450_);
    return v___x_1452_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25() -> *mut leanh::LeanObject
{
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1456_ = leanh::lean_box(0);
    v___x_1457_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__24;
    v___x_1458_ = l_Lean_mkConst(v___x_1457_, v___x_1456_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29() -> *mut leanh::LeanObject
{
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = leanh::lean_box(0);
    v___x_1465_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__28;
    v___x_1466_ = l_Lean_mkConst(v___x_1465_, v___x_1464_);
    return v___x_1466_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32() -> *mut leanh::LeanObject
{
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1471_ = leanh::lean_box(0);
    v___x_1472_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__31;
    v___x_1473_ = l_Lean_mkConst(v___x_1472_, v___x_1471_);
    return v___x_1473_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35() -> *mut leanh::LeanObject
{
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = leanh::lean_box(0);
    v___x_1478_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__34;
    v___x_1479_ = l_Lean_mkConst(v___x_1478_, v___x_1477_);
    return v___x_1479_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38() -> *mut leanh::LeanObject
{
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = leanh::lean_box(0);
    v___x_1484_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__37;
    v___x_1485_ = l_Lean_mkConst(v___x_1484_, v___x_1483_);
    return v___x_1485_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43() -> *mut leanh::LeanObject
{
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__42;
    v___x_1495_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__41;
    v___x_1496_ = l_Lean_mkConst(v___x_1495_, v___x_1494_);
    return v___x_1496_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44() -> *mut leanh::LeanObject
{
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once),
        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38,
    );
    v___x_1498_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__43),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__43_once),
        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__43,
    );
    v___x_1499_ = l_Lean_Expr_app___override(v___x_1498_, v___x_1497_);
    return v___x_1499_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47() -> *mut leanh::LeanObject
{
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__42;
    v___x_1505_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__46;
    v___x_1506_ = l_Lean_mkConst(v___x_1505_, v___x_1504_);
    return v___x_1506_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50() -> *mut leanh::LeanObject
{
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = leanh::lean_box(0);
    v___x_1511_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__49;
    v___x_1512_ = l_Lean_mkConst(v___x_1511_, v___x_1510_);
    return v___x_1512_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_toExprM(
    mut v_pu_1513_: u8,
    mut v_code_1514_: *mut leanh::LeanObject,
    mut v_a_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1534_: u8 = 0;
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v_fvarId_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1544_: usize = 0;
    let mut v___x_1545_: usize = 0;
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1556_: u8 = 0;
    let mut v_cases_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1560_: usize = 0;
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut v_fvarId_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: u8 = 0;
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1614_: u8 = 0;
    let mut v_fvarId_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1640_: u8 = 0;
    let mut v_fvarId_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u8 = 0;
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v_fvarId_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1681_: u8 = 0;
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1693_: u8 = 0;
    let mut v_fvarId_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1696_: u8 = 0;
    let mut v_persistent_1697_: u8 = 0;
    let mut v_k_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v_value_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: u8 = 0;
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1722_: u8 = 0;
    let mut v___y_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1731_: u8 = 0;
    let mut v_persistent_1732_: u8 = 0;
    let mut v_objs_x3f_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: u8 = 0;
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1774_: u8 = 0;
    let mut v_fvarId_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1785_: u8 = 0;
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v_decl_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_code_1514_) {
                0 => {
                    v_decl_1517_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_ref(v_decl_1517_);
                    v_k_1518_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc_ref(v_k_1518_);
                    leanh::lean_dec_ref_known(v_code_1514_, 2);
                    v_fvarId_1519_ = leanh::lean_ctor_get(v_decl_1517_, 0);
                    leanh::lean_inc(v_fvarId_1519_);
                    v_binderName_1520_ = leanh::lean_ctor_get(v_decl_1517_, 1);
                    leanh::lean_inc(v_binderName_1520_);
                    v_type_1521_ = leanh::lean_ctor_get(v_decl_1517_, 2);
                    leanh::lean_inc_ref(v_type_1521_);
                    v_value_1522_ = leanh::lean_ctor_get(v_decl_1517_, 3);
                    leanh::lean_inc(v_value_1522_);
                    leanh::lean_dec_ref(v_decl_1517_);
                    v___x_1523_ =
                        l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                            v_a_1516_,
                            v_a_1515_,
                            v_type_1521_,
                        );
                    v___x_1524_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_1513_, v_value_1522_);
                    v___x_1525_ =
                        l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                            v_a_1516_,
                            v_a_1515_,
                            v___x_1524_,
                        );
                    leanh::lean_inc(v_a_1515_);
                    v___x_1526_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1519_, v_a_1515_, v_a_1516_);
                    v___x_1527_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1528_ = lean_nat_add(v_a_1515_, v___x_1527_);
                    v___x_1529_ = l_Lean_Compiler_LCNF_Code_toExprM(
                        v_pu_1513_,
                        v_k_1518_,
                        v___x_1528_,
                        v___x_1526_,
                    );
                    leanh::lean_dec(v___x_1528_);
                    v_fst_1530_ = leanh::lean_ctor_get(v___x_1529_, 0);
                    v_snd_1531_ = leanh::lean_ctor_get(v___x_1529_, 1);
                    v_isSharedCheck_1540_ = (!leanh::lean_is_exclusive(v___x_1529_)) as u8;
                    if v_isSharedCheck_1540_ == 0 {
                        v___x_1533_ = v___x_1529_;
                        v_isShared_1534_ = v_isSharedCheck_1540_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1531_);
                        leanh::lean_inc(v_fst_1530_);
                        leanh::lean_dec(v___x_1529_);
                        v___x_1533_ = leanh::lean_box(0);
                        v_isShared_1534_ = v_isSharedCheck_1540_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_fvarId_1541_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc(v_fvarId_1541_);
                    v_args_1542_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc_ref(v_args_1542_);
                    leanh::lean_dec_ref_known(v_code_1514_, 2);
                    v___x_1543_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(
                        v_a_1515_,
                        v_a_1516_,
                        v_fvarId_1541_,
                    );
                    v_sz_1544_ = lean_array_size(v_args_1542_);
                    v___x_1545_ = 0usize;
                    v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_1544_, v___x_1545_, v_args_1542_, v_a_1515_, v_a_1516_);
                    v_fst_1547_ = leanh::lean_ctor_get(v___x_1546_, 0);
                    v_snd_1548_ = leanh::lean_ctor_get(v___x_1546_, 1);
                    v_isSharedCheck_1556_ = (!leanh::lean_is_exclusive(v___x_1546_)) as u8;
                    if v_isSharedCheck_1556_ == 0 {
                        v___x_1550_ = v___x_1546_;
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1548_);
                        leanh::lean_inc(v_fst_1547_);
                        leanh::lean_dec(v___x_1546_);
                        v___x_1550_ = leanh::lean_box(0);
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 3;
                        continue;
                    }
                }
                4 => {
                    v_cases_1557_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_ref(v_cases_1557_);
                    leanh::lean_dec_ref_known(v_code_1514_, 1);
                    v_discr_1558_ = leanh::lean_ctor_get(v_cases_1557_, 2);
                    leanh::lean_inc(v_discr_1558_);
                    v_alts_1559_ = leanh::lean_ctor_get(v_cases_1557_, 3);
                    leanh::lean_inc_ref(v_alts_1559_);
                    leanh::lean_dec_ref(v_cases_1557_);
                    v_sz_1560_ = lean_array_size(v_alts_1559_);
                    v___x_1561_ = 0usize;
                    v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_1513_, v_sz_1560_, v___x_1561_, v_alts_1559_, v_a_1515_, v_a_1516_);
                    v_fst_1563_ = leanh::lean_ctor_get(v___x_1562_, 0);
                    v_snd_1564_ = leanh::lean_ctor_get(v___x_1562_, 1);
                    v_isSharedCheck_1578_ = (!leanh::lean_is_exclusive(v___x_1562_)) as u8;
                    if v_isSharedCheck_1578_ == 0 {
                        v___x_1566_ = v___x_1562_;
                        v_isShared_1567_ = v_isSharedCheck_1578_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1564_);
                        leanh::lean_inc(v_fst_1563_);
                        leanh::lean_dec(v___x_1562_);
                        v___x_1566_ = leanh::lean_box(0);
                        v_isShared_1567_ = v_isSharedCheck_1578_;
                        state = 5;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_1579_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc(v_fvarId_1579_);
                    leanh::lean_dec_ref_known(v_code_1514_, 1);
                    v___x_1580_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(
                        v_a_1515_,
                        v_a_1516_,
                        v_fvarId_1579_,
                    );
                    v___x_1581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1581_, 0, v___x_1580_);
                    leanh::lean_ctor_set(v___x_1581_, 1, v_a_1516_);
                    return v___x_1581_;
                }
                6 => {
                    v_type_1582_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_ref(v_type_1582_);
                    leanh::lean_dec_ref_known(v_code_1514_, 1);
                    v___x_1583_ =
                        l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                            v_a_1516_,
                            v_a_1515_,
                            v_type_1582_,
                        );
                    v___x_1584_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__5_once),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__5,
                    );
                    v___x_1585_ = l_Lean_Expr_app___override(v___x_1584_, v___x_1583_);
                    v___x_1586_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
                    leanh::lean_ctor_set(v___x_1586_, 1, v_a_1516_);
                    return v___x_1586_;
                }
                7 => {
                    v_fvarId_1587_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_n(v_fvarId_1587_, 2);
                    v_i_1588_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc(v_i_1588_);
                    v_y_1589_ = leanh::lean_ctor_get(v_code_1514_, 2);
                    leanh::lean_inc(v_y_1589_);
                    v_k_1590_ = leanh::lean_ctor_get(v_code_1514_, 3);
                    leanh::lean_inc_ref(v_k_1590_);
                    leanh::lean_dec_ref_known(v_code_1514_, 4);
                    v___x_1591_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_Arg_toExprM___redArg(v_y_1589_, v_a_1515_, v_a_1516_);
                    v_fst_1592_ = leanh::lean_ctor_get(v___x_1591_, 0);
                    leanh::lean_inc(v_fst_1592_);
                    v_snd_1593_ = leanh::lean_ctor_get(v___x_1591_, 1);
                    leanh::lean_inc(v_snd_1593_);
                    leanh::lean_dec_ref(v___x_1591_);
                    v___x_1594_ = l_Lean_Expr_fvar___override(v_fvarId_1587_);
                    leanh::lean_inc(v_a_1515_);
                    v___x_1595_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1587_, v_a_1515_, v_snd_1593_);
                    v___x_1596_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1597_ = lean_nat_add(v_a_1515_, v___x_1596_);
                    v___x_1598_ = l_Lean_Compiler_LCNF_Code_toExprM(
                        v_pu_1513_,
                        v_k_1590_,
                        v___x_1597_,
                        v___x_1595_,
                    );
                    leanh::lean_dec(v___x_1597_);
                    v_fst_1599_ = leanh::lean_ctor_get(v___x_1598_, 0);
                    v_snd_1600_ = leanh::lean_ctor_get(v___x_1598_, 1);
                    v_isSharedCheck_1614_ = (!leanh::lean_is_exclusive(v___x_1598_)) as u8;
                    if v_isSharedCheck_1614_ == 0 {
                        v___x_1602_ = v___x_1598_;
                        v_isShared_1603_ = v_isSharedCheck_1614_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1600_);
                        leanh::lean_inc(v_fst_1599_);
                        leanh::lean_dec(v___x_1598_);
                        v___x_1602_ = leanh::lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1614_;
                        state = 7;
                        continue;
                    }
                }
                8 => {
                    v_fvarId_1615_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_n(v_fvarId_1615_, 2);
                    v_i_1616_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc(v_i_1616_);
                    v_y_1617_ = leanh::lean_ctor_get(v_code_1514_, 2);
                    leanh::lean_inc(v_y_1617_);
                    v_k_1618_ = leanh::lean_ctor_get(v_code_1514_, 3);
                    leanh::lean_inc_ref(v_k_1618_);
                    leanh::lean_dec_ref_known(v_code_1514_, 4);
                    v___x_1619_ = l_Lean_Expr_fvar___override(v_fvarId_1615_);
                    leanh::lean_inc(v_a_1515_);
                    v___x_1620_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1615_, v_a_1515_, v_a_1516_);
                    v___x_1621_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1622_ = lean_nat_add(v_a_1515_, v___x_1621_);
                    v___x_1623_ = l_Lean_Compiler_LCNF_Code_toExprM(
                        v_pu_1513_,
                        v_k_1618_,
                        v___x_1622_,
                        v___x_1620_,
                    );
                    leanh::lean_dec(v___x_1622_);
                    v_fst_1624_ = leanh::lean_ctor_get(v___x_1623_, 0);
                    v_snd_1625_ = leanh::lean_ctor_get(v___x_1623_, 1);
                    v_isSharedCheck_1640_ = (!leanh::lean_is_exclusive(v___x_1623_)) as u8;
                    if v_isSharedCheck_1640_ == 0 {
                        v___x_1627_ = v___x_1623_;
                        v_isShared_1628_ = v_isSharedCheck_1640_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1625_);
                        leanh::lean_inc(v_fst_1624_);
                        leanh::lean_dec(v___x_1623_);
                        v___x_1627_ = leanh::lean_box(0);
                        v_isShared_1628_ = v_isSharedCheck_1640_;
                        state = 9;
                        continue;
                    }
                }
                9 => {
                    v_fvarId_1641_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_n(v_fvarId_1641_, 2);
                    v_i_1642_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc(v_i_1642_);
                    v_offset_1643_ = leanh::lean_ctor_get(v_code_1514_, 2);
                    leanh::lean_inc(v_offset_1643_);
                    v_y_1644_ = leanh::lean_ctor_get(v_code_1514_, 3);
                    leanh::lean_inc(v_y_1644_);
                    v_ty_1645_ = leanh::lean_ctor_get(v_code_1514_, 4);
                    leanh::lean_inc_ref(v_ty_1645_);
                    v_k_1646_ = leanh::lean_ctor_get(v_code_1514_, 5);
                    leanh::lean_inc_ref(v_k_1646_);
                    leanh::lean_dec_ref_known(v_code_1514_, 6);
                    v___x_1647_ = l_Lean_Expr_fvar___override(v_fvarId_1641_);
                    leanh::lean_inc(v_a_1515_);
                    v___x_1648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1641_, v_a_1515_, v_a_1516_);
                    v___x_1649_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1650_ = lean_nat_add(v_a_1515_, v___x_1649_);
                    v___x_1651_ = l_Lean_Compiler_LCNF_Code_toExprM(
                        v_pu_1513_,
                        v_k_1646_,
                        v___x_1650_,
                        v___x_1648_,
                    );
                    leanh::lean_dec(v___x_1650_);
                    v_fst_1652_ = leanh::lean_ctor_get(v___x_1651_, 0);
                    v_snd_1653_ = leanh::lean_ctor_get(v___x_1651_, 1);
                    v_isSharedCheck_1669_ = (!leanh::lean_is_exclusive(v___x_1651_)) as u8;
                    if v_isSharedCheck_1669_ == 0 {
                        v___x_1655_ = v___x_1651_;
                        v_isShared_1656_ = v_isSharedCheck_1669_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1653_);
                        leanh::lean_inc(v_fst_1652_);
                        leanh::lean_dec(v___x_1651_);
                        v___x_1655_ = leanh::lean_box(0);
                        v_isShared_1656_ = v_isSharedCheck_1669_;
                        state = 11;
                        continue;
                    }
                }
                10 => {
                    v_fvarId_1670_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_n(v_fvarId_1670_, 2);
                    v_cidx_1671_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc(v_cidx_1671_);
                    v_k_1672_ = leanh::lean_ctor_get(v_code_1514_, 2);
                    leanh::lean_inc_ref(v_k_1672_);
                    leanh::lean_dec_ref_known(v_code_1514_, 3);
                    leanh::lean_inc(v_a_1515_);
                    v___x_1673_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1670_, v_a_1515_, v_a_1516_);
                    v___x_1674_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1675_ = lean_nat_add(v_a_1515_, v___x_1674_);
                    v___x_1676_ = l_Lean_Compiler_LCNF_Code_toExprM(
                        v_pu_1513_,
                        v_k_1672_,
                        v___x_1675_,
                        v___x_1673_,
                    );
                    leanh::lean_dec(v___x_1675_);
                    v_fst_1677_ = leanh::lean_ctor_get(v___x_1676_, 0);
                    v_snd_1678_ = leanh::lean_ctor_get(v___x_1676_, 1);
                    v_isSharedCheck_1693_ = (!leanh::lean_is_exclusive(v___x_1676_)) as u8;
                    if v_isSharedCheck_1693_ == 0 {
                        v___x_1680_ = v___x_1676_;
                        v_isShared_1681_ = v_isSharedCheck_1693_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1678_);
                        leanh::lean_inc(v_fst_1677_);
                        leanh::lean_dec(v___x_1676_);
                        v___x_1680_ = leanh::lean_box(0);
                        v_isShared_1681_ = v_isSharedCheck_1693_;
                        state = 13;
                        continue;
                    }
                }
                11 => {
                    v_fvarId_1694_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_n(v_fvarId_1694_, 2);
                    v_n_1695_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc(v_n_1695_);
                    v_check_1696_ = leanh::lean_ctor_get_uint8(
                        v_code_1514_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_1697_ = leanh::lean_ctor_get_uint8(
                        v_code_1514_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_1698_ = leanh::lean_ctor_get(v_code_1514_, 2);
                    leanh::lean_inc_ref(v_k_1698_);
                    leanh::lean_dec_ref_known(v_code_1514_, 3);
                    v___x_1699_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__25),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_toExprM___closed__25_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__25,
                    );
                    v___x_1700_ = l_Lean_Expr_fvar___override(v_fvarId_1694_);
                    v___x_1701_ = l_Lean_mkNatLit(v_n_1695_);
                    if v_check_1696_ == 0 {
                        v___x_1727_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__29),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29,
                        );
                        v___y_1724_ = v___x_1727_;
                        state = 18;
                        continue;
                    } else {
                        v___x_1728_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__32),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32,
                        );
                        v___y_1724_ = v___x_1728_;
                        state = 18;
                        continue;
                    }
                }
                12 => {
                    v_fvarId_1729_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_n(v_fvarId_1729_, 2);
                    v_n_1730_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc(v_n_1730_);
                    v_check_1731_ = leanh::lean_ctor_get_uint8(
                        v_code_1514_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_1732_ = leanh::lean_ctor_get_uint8(
                        v_code_1514_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_1733_ = leanh::lean_ctor_get(v_code_1514_, 2);
                    leanh::lean_inc(v_objs_x3f_1733_);
                    v_k_1734_ = leanh::lean_ctor_get(v_code_1514_, 3);
                    leanh::lean_inc_ref(v_k_1734_);
                    leanh::lean_dec_ref_known(v_code_1514_, 4);
                    leanh::lean_inc(v_a_1515_);
                    v___x_1735_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1729_, v_a_1515_, v_a_1516_);
                    v___x_1736_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1737_ = lean_nat_add(v_a_1515_, v___x_1736_);
                    v___x_1738_ = l_Lean_Compiler_LCNF_Code_toExprM(
                        v_pu_1513_,
                        v_k_1734_,
                        v___x_1737_,
                        v___x_1735_,
                    );
                    leanh::lean_dec(v___x_1737_);
                    v_fst_1739_ = leanh::lean_ctor_get(v___x_1738_, 0);
                    v_snd_1740_ = leanh::lean_ctor_get(v___x_1738_, 1);
                    v_isSharedCheck_1774_ = (!leanh::lean_is_exclusive(v___x_1738_)) as u8;
                    if v_isSharedCheck_1774_ == 0 {
                        v___x_1742_ = v___x_1738_;
                        v_isShared_1743_ = v_isSharedCheck_1774_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1740_);
                        leanh::lean_inc(v_fst_1739_);
                        leanh::lean_dec(v___x_1738_);
                        v___x_1742_ = leanh::lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1774_;
                        state = 19;
                        continue;
                    }
                }
                13 => {
                    v_fvarId_1775_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_n(v_fvarId_1775_, 2);
                    v_k_1776_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc_ref(v_k_1776_);
                    leanh::lean_dec_ref_known(v_code_1514_, 2);
                    leanh::lean_inc(v_a_1515_);
                    v___x_1777_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1775_, v_a_1515_, v_a_1516_);
                    v___x_1778_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1779_ = lean_nat_add(v_a_1515_, v___x_1778_);
                    v___x_1780_ = l_Lean_Compiler_LCNF_Code_toExprM(
                        v_pu_1513_,
                        v_k_1776_,
                        v___x_1779_,
                        v___x_1777_,
                    );
                    leanh::lean_dec(v___x_1779_);
                    v_fst_1781_ = leanh::lean_ctor_get(v___x_1780_, 0);
                    v_snd_1782_ = leanh::lean_ctor_get(v___x_1780_, 1);
                    v_isSharedCheck_1796_ = (!leanh::lean_is_exclusive(v___x_1780_)) as u8;
                    if v_isSharedCheck_1796_ == 0 {
                        v___x_1784_ = v___x_1780_;
                        v_isShared_1785_ = v_isSharedCheck_1796_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1782_);
                        leanh::lean_inc(v_fst_1781_);
                        leanh::lean_dec(v___x_1780_);
                        v___x_1784_ = leanh::lean_box(0);
                        v_isShared_1785_ = v_isSharedCheck_1796_;
                        state = 24;
                        continue;
                    }
                }
                _ => {
                    v_decl_1797_ = leanh::lean_ctor_get(v_code_1514_, 0);
                    leanh::lean_inc_ref(v_decl_1797_);
                    v_k_1798_ = leanh::lean_ctor_get(v_code_1514_, 1);
                    leanh::lean_inc_ref(v_k_1798_);
                    leanh::lean_dec_ref(v_code_1514_);
                    v_fvarId_1799_ = leanh::lean_ctor_get(v_decl_1797_, 0);
                    leanh::lean_inc(v_fvarId_1799_);
                    v_binderName_1800_ = leanh::lean_ctor_get(v_decl_1797_, 1);
                    leanh::lean_inc(v_binderName_1800_);
                    v_type_1801_ = leanh::lean_ctor_get(v_decl_1797_, 3);
                    leanh::lean_inc_ref(v_type_1801_);
                    v___x_1802_ =
                        l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(
                            v_a_1516_,
                            v_a_1515_,
                            v_type_1801_,
                        );
                    v___x_1803_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(
                        v_pu_1513_,
                        v_decl_1797_,
                        v_a_1515_,
                        v_a_1516_,
                    );
                    v_fst_1804_ = leanh::lean_ctor_get(v___x_1803_, 0);
                    leanh::lean_inc(v_fst_1804_);
                    v_snd_1805_ = leanh::lean_ctor_get(v___x_1803_, 1);
                    leanh::lean_inc(v_snd_1805_);
                    leanh::lean_dec_ref(v___x_1803_);
                    leanh::lean_inc(v_a_1515_);
                    v___x_1806_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1799_, v_a_1515_, v_snd_1805_);
                    v___x_1807_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1808_ = lean_nat_add(v_a_1515_, v___x_1807_);
                    v___x_1809_ = l_Lean_Compiler_LCNF_Code_toExprM(
                        v_pu_1513_,
                        v_k_1798_,
                        v___x_1808_,
                        v___x_1806_,
                    );
                    leanh::lean_dec(v___x_1808_);
                    v_fst_1810_ = leanh::lean_ctor_get(v___x_1809_, 0);
                    v_snd_1811_ = leanh::lean_ctor_get(v___x_1809_, 1);
                    v_isSharedCheck_1820_ = (!leanh::lean_is_exclusive(v___x_1809_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1813_ = v___x_1809_;
                        v_isShared_1814_ = v_isSharedCheck_1820_;
                        state = 26;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1811_);
                        leanh::lean_inc(v_fst_1810_);
                        leanh::lean_dec(v___x_1809_);
                        v___x_1813_ = leanh::lean_box(0);
                        v_isShared_1814_ = v_isSharedCheck_1820_;
                        state = 26;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1535_ = 1;
                v___x_1536_ = l_Lean_Expr_letE___override(
                    v_binderName_1520_,
                    v___x_1523_,
                    v___x_1525_,
                    v_fst_1530_,
                    v___x_1535_,
                );
                if v_isShared_1534_ == 0 {
                    leanh::lean_ctor_set(v___x_1533_, 0, v___x_1536_);
                    v___x_1538_ = v___x_1533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1539_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_snd_1531_);
                    v___x_1538_ = v_reuseFailAlloc_1539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1538_;
            }
            3 => {
                v___x_1552_ = l_Lean_mkAppN(v___x_1543_, v_fst_1547_);
                leanh::lean_dec(v_fst_1547_);
                if v_isShared_1551_ == 0 {
                    leanh::lean_ctor_set(v___x_1550_, 0, v___x_1552_);
                    v___x_1554_ = v___x_1550_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1555_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_snd_1548_);
                    v___x_1554_ = v_reuseFailAlloc_1555_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1554_;
            }
            5 => {
                v___x_1568_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_FVarId_toExpr(
                    v_a_1515_,
                    v_snd_1564_,
                    v_discr_1558_,
                );
                v___x_1569_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__2_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__2,
                );
                v___x_1570_ = leanh::lean_unsigned_to_nat(1);
                v___x_1571_ = lean_mk_empty_array_with_capacity(v___x_1570_);
                v___x_1572_ = lean_array_push(v___x_1571_, v___x_1568_);
                v___x_1573_ = l_Array_append___redArg(v___x_1572_, v_fst_1563_);
                leanh::lean_dec(v_fst_1563_);
                v___x_1574_ = l_Lean_mkAppN(v___x_1569_, v___x_1573_);
                leanh::lean_dec_ref(v___x_1573_);
                if v_isShared_1567_ == 0 {
                    leanh::lean_ctor_set(v___x_1566_, 0, v___x_1574_);
                    v___x_1576_ = v___x_1566_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_snd_1564_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1576_;
            }
            7 => {
                v___x_1604_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__8_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__8,
                );
                v___x_1605_ = l_Lean_mkNatLit(v_i_1588_);
                v___x_1606_ = l_Lean_mkApp3(v___x_1604_, v___x_1594_, v___x_1605_, v_fst_1592_);
                v___x_1607_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__10;
                v___x_1608_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13,
                );
                v___x_1609_ = 1;
                v___x_1610_ = l_Lean_Expr_letE___override(
                    v___x_1607_,
                    v___x_1608_,
                    v___x_1606_,
                    v_fst_1599_,
                    v___x_1609_,
                );
                if v_isShared_1603_ == 0 {
                    leanh::lean_ctor_set(v___x_1602_, 0, v___x_1610_);
                    v___x_1612_ = v___x_1602_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1613_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_snd_1600_);
                    v___x_1612_ = v_reuseFailAlloc_1613_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1612_;
            }
            9 => {
                v___x_1629_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__16),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__16_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__16,
                );
                v___x_1630_ = l_Lean_mkNatLit(v_i_1616_);
                v___x_1631_ = l_Lean_Expr_fvar___override(v_y_1617_);
                v_value_1632_ = l_Lean_mkApp3(v___x_1629_, v___x_1619_, v___x_1630_, v___x_1631_);
                v___x_1633_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__10;
                v___x_1634_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13,
                );
                v___x_1635_ = 1;
                v___x_1636_ = l_Lean_Expr_letE___override(
                    v___x_1633_,
                    v___x_1634_,
                    v_value_1632_,
                    v_fst_1624_,
                    v___x_1635_,
                );
                if v_isShared_1628_ == 0 {
                    leanh::lean_ctor_set(v___x_1627_, 0, v___x_1636_);
                    v___x_1638_ = v___x_1627_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1639_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_snd_1625_);
                    v___x_1638_ = v_reuseFailAlloc_1639_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1638_;
            }
            11 => {
                v___x_1657_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__19),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__19_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__19,
                );
                v___x_1658_ = l_Lean_mkNatLit(v_i_1642_);
                v___x_1659_ = l_Lean_mkNatLit(v_offset_1643_);
                v___x_1660_ = l_Lean_Expr_fvar___override(v_y_1644_);
                v_value_1661_ = l_Lean_mkApp5(
                    v___x_1657_,
                    v___x_1647_,
                    v___x_1658_,
                    v___x_1659_,
                    v___x_1660_,
                    v_ty_1645_,
                );
                v___x_1662_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__10;
                v___x_1663_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13,
                );
                v___x_1664_ = 1;
                v___x_1665_ = l_Lean_Expr_letE___override(
                    v___x_1662_,
                    v___x_1663_,
                    v_value_1661_,
                    v_fst_1652_,
                    v___x_1664_,
                );
                if v_isShared_1656_ == 0 {
                    leanh::lean_ctor_set(v___x_1655_, 0, v___x_1665_);
                    v___x_1667_ = v___x_1655_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1668_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_snd_1653_);
                    v___x_1667_ = v_reuseFailAlloc_1668_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1667_;
            }
            13 => {
                v___x_1682_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__22),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__22_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__22,
                );
                v___x_1683_ = l_Lean_Expr_fvar___override(v_fvarId_1670_);
                v___x_1684_ = l_Lean_mkNatLit(v_cidx_1671_);
                v___x_1685_ = l_Lean_mkAppB(v___x_1682_, v___x_1683_, v___x_1684_);
                v___x_1686_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__10;
                v___x_1687_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13,
                );
                v___x_1688_ = 1;
                v___x_1689_ = l_Lean_Expr_letE___override(
                    v___x_1686_,
                    v___x_1687_,
                    v___x_1685_,
                    v_fst_1677_,
                    v___x_1688_,
                );
                if v_isShared_1681_ == 0 {
                    leanh::lean_ctor_set(v___x_1680_, 0, v___x_1689_);
                    v___x_1691_ = v___x_1680_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1692_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_snd_1678_);
                    v___x_1691_ = v_reuseFailAlloc_1692_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1691_;
            }
            15 => {
                leanh::lean_inc(v_a_1515_);
                v___x_1705_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1694_, v_a_1515_, v_a_1516_);
                v___x_1706_ = leanh::lean_unsigned_to_nat(1);
                v___x_1707_ = lean_nat_add(v_a_1515_, v___x_1706_);
                v___x_1708_ = l_Lean_Compiler_LCNF_Code_toExprM(
                    v_pu_1513_,
                    v_k_1698_,
                    v___x_1707_,
                    v___x_1705_,
                );
                leanh::lean_dec(v___x_1707_);
                v_fst_1709_ = leanh::lean_ctor_get(v___x_1708_, 0);
                v_snd_1710_ = leanh::lean_ctor_get(v___x_1708_, 1);
                v_isSharedCheck_1722_ = (!leanh::lean_is_exclusive(v___x_1708_)) as u8;
                if v_isSharedCheck_1722_ == 0 {
                    v___x_1712_ = v___x_1708_;
                    v_isShared_1713_ = v_isSharedCheck_1722_;
                    state = 16;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1710_);
                    leanh::lean_inc(v_fst_1709_);
                    leanh::lean_dec(v___x_1708_);
                    v___x_1712_ = leanh::lean_box(0);
                    v_isShared_1713_ = v_isSharedCheck_1722_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                leanh::lean_inc_ref(v___y_1704_);
                leanh::lean_inc_ref(v___y_1703_);
                v_value_1714_ = l_Lean_mkApp4(
                    v___x_1699_,
                    v___x_1700_,
                    v___x_1701_,
                    v___y_1703_,
                    v___y_1704_,
                );
                v___x_1715_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__10;
                v___x_1716_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13,
                );
                v___x_1717_ = 1;
                v___x_1718_ = l_Lean_Expr_letE___override(
                    v___x_1715_,
                    v___x_1716_,
                    v_value_1714_,
                    v_fst_1709_,
                    v___x_1717_,
                );
                if v_isShared_1713_ == 0 {
                    leanh::lean_ctor_set(v___x_1712_, 0, v___x_1718_);
                    v___x_1720_ = v___x_1712_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1721_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_snd_1710_);
                    v___x_1720_ = v_reuseFailAlloc_1721_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1720_;
            }
            18 => {
                if v_persistent_1697_ == 0 {
                    v___x_1725_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__29),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29,
                    );
                    v___y_1703_ = v___y_1724_;
                    v___y_1704_ = v___x_1725_;
                    state = 15;
                    continue;
                } else {
                    v___x_1726_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__32),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32,
                    );
                    v___y_1703_ = v___y_1724_;
                    v___y_1704_ = v___x_1726_;
                    state = 15;
                    continue;
                }
            }
            19 => {
                v___x_1744_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__35),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__35_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__35,
                );
                v___x_1745_ = l_Lean_Expr_fvar___override(v_fvarId_1729_);
                v___x_1746_ = l_Lean_mkNatLit(v_n_1730_);
                if v_check_1731_ == 0 {
                    v___x_1772_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__29),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29,
                    );
                    v___y_1769_ = v___x_1772_;
                    state = 23;
                    continue;
                } else {
                    v___x_1773_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__32),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32,
                    );
                    v___y_1769_ = v___x_1773_;
                    state = 23;
                    continue;
                }
            }
            20 => {
                leanh::lean_inc_ref(v___y_1748_);
                leanh::lean_inc_ref(v___y_1749_);
                v___x_1751_ = l_Lean_mkApp5(
                    v___x_1744_,
                    v___x_1745_,
                    v___x_1746_,
                    v___y_1749_,
                    v___y_1748_,
                    v___y_1750_,
                );
                v___x_1752_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__10;
                v___x_1753_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13,
                );
                v___x_1754_ = 1;
                v___x_1755_ = l_Lean_Expr_letE___override(
                    v___x_1752_,
                    v___x_1753_,
                    v___x_1751_,
                    v_fst_1739_,
                    v___x_1754_,
                );
                if v_isShared_1743_ == 0 {
                    leanh::lean_ctor_set(v___x_1742_, 0, v___x_1755_);
                    v___x_1757_ = v___x_1742_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1758_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_snd_1740_);
                    v___x_1757_ = v_reuseFailAlloc_1758_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1757_;
            }
            22 => {
                v___x_1762_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__38),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__38_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__38,
                );
                if leanh::lean_obj_tag(v_objs_x3f_1733_) == 0 {
                    v___x_1763_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__44),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_toExprM___closed__44_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__44,
                    );
                    v___y_1748_ = v___y_1761_;
                    v___y_1749_ = v___y_1760_;
                    v___y_1750_ = v___x_1763_;
                    state = 20;
                    continue;
                } else {
                    v_val_1764_ = leanh::lean_ctor_get(v_objs_x3f_1733_, 0);
                    leanh::lean_inc(v_val_1764_);
                    leanh::lean_dec_ref_known(v_objs_x3f_1733_, 1);
                    v___x_1765_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__47),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_toExprM___closed__47_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__47,
                    );
                    v___x_1766_ = l_Lean_mkNatLit(v_val_1764_);
                    v___x_1767_ = l_Lean_mkAppB(v___x_1765_, v___x_1762_, v___x_1766_);
                    v___y_1748_ = v___y_1761_;
                    v___y_1749_ = v___y_1760_;
                    v___y_1750_ = v___x_1767_;
                    state = 20;
                    continue;
                }
            }
            23 => {
                if v_persistent_1732_ == 0 {
                    v___x_1770_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__29),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_toExprM___closed__29_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__29,
                    );
                    v___y_1760_ = v___y_1769_;
                    v___y_1761_ = v___x_1770_;
                    state = 22;
                    continue;
                } else {
                    v___x_1771_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__32),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_toExprM___closed__32_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__32,
                    );
                    v___y_1760_ = v___y_1769_;
                    v___y_1761_ = v___x_1771_;
                    state = 22;
                    continue;
                }
            }
            24 => {
                v___x_1786_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__50),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__50_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__50,
                );
                v___x_1787_ = l_Lean_Expr_fvar___override(v_fvarId_1775_);
                v___x_1788_ = l_Lean_Expr_app___override(v___x_1786_, v___x_1787_);
                v___x_1789_ = l_Lean_Compiler_LCNF_Code_toExprM___closed__10;
                v___x_1790_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_toExprM___closed__13_once),
                    _init_l_Lean_Compiler_LCNF_Code_toExprM___closed__13,
                );
                v___x_1791_ = 1;
                v___x_1792_ = l_Lean_Expr_letE___override(
                    v___x_1789_,
                    v___x_1790_,
                    v___x_1788_,
                    v_fst_1781_,
                    v___x_1791_,
                );
                if v_isShared_1785_ == 0 {
                    leanh::lean_ctor_set(v___x_1784_, 0, v___x_1792_);
                    v___x_1794_ = v___x_1784_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1795_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_snd_1782_);
                    v___x_1794_ = v_reuseFailAlloc_1795_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1794_;
            }
            26 => {
                v___x_1815_ = 1;
                v___x_1816_ = l_Lean_Expr_letE___override(
                    v_binderName_1800_,
                    v___x_1802_,
                    v_fst_1804_,
                    v_fst_1810_,
                    v___x_1815_,
                );
                if v_isShared_1814_ == 0 {
                    leanh::lean_ctor_set(v___x_1813_, 0, v___x_1816_);
                    v___x_1818_ = v___x_1813_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1819_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_snd_1811_);
                    v___x_1818_ = v_reuseFailAlloc_1819_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(
    mut v_pu_1821_: u8,
    mut v_value_1822_: *mut leanh::LeanObject,
    mut v_params_1823_: *mut leanh::LeanObject,
    mut v_params_1824_: *mut leanh::LeanObject,
    mut v_i_1825_: *mut leanh::LeanObject,
    mut v_a_1826_: *mut leanh::LeanObject,
    mut v_a_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1841_: u8 = 0;
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1828_ = lean_array_get_size(v_params_1824_);
                v___x_1829_ = lean_nat_dec_lt(v_i_1825_, v___x_1828_);
                if v___x_1829_ == 0 {
                    leanh::lean_dec(v_i_1825_);
                    v___x_1830_ = l_Lean_Compiler_LCNF_Code_toExprM(
                        v_pu_1821_,
                        v_value_1822_,
                        v_a_1826_,
                        v_a_1827_,
                    );
                    v_fst_1831_ = leanh::lean_ctor_get(v___x_1830_, 0);
                    v_snd_1832_ = leanh::lean_ctor_get(v___x_1830_, 1);
                    v_isSharedCheck_1841_ = (!leanh::lean_is_exclusive(v___x_1830_)) as u8;
                    if v_isSharedCheck_1841_ == 0 {
                        v___x_1834_ = v___x_1830_;
                        v_isShared_1835_ = v_isSharedCheck_1841_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1832_);
                        leanh::lean_inc(v_fst_1831_);
                        leanh::lean_dec(v___x_1830_);
                        v___x_1834_ = leanh::lean_box(0);
                        v_isShared_1835_ = v_isSharedCheck_1841_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1842_ = lean_array_fget_borrowed(v_params_1824_, v_i_1825_);
                    v_fvarId_1843_ = leanh::lean_ctor_get(v___x_1842_, 0);
                    v___x_1844_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1845_ = lean_nat_add(v_i_1825_, v___x_1844_);
                    leanh::lean_dec(v_i_1825_);
                    leanh::lean_inc(v_a_1826_);
                    leanh::lean_inc(v_fvarId_1843_);
                    v___x_1846_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1843_, v_a_1826_, v_a_1827_);
                    v___x_1847_ = lean_nat_add(v_a_1826_, v___x_1844_);
                    leanh::lean_dec(v_a_1826_);
                    v_i_1825_ = v___x_1845_;
                    v_a_1826_ = v___x_1847_;
                    v_a_1827_ = v___x_1846_;
                    state = 0;
                    continue;
                }
            }
            1 => {
                v___x_1836_ = lean_array_get_size(v_params_1823_);
                v___x_1837_ =
                    l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(
                        v_pu_1821_,
                        v_params_1823_,
                        v_a_1826_,
                        v_snd_1832_,
                        v___x_1836_,
                        v_fst_1831_,
                    );
                if v_isShared_1835_ == 0 {
                    leanh::lean_ctor_set(v___x_1834_, 0, v___x_1837_);
                    v___x_1839_ = v___x_1834_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1840_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_snd_1832_);
                    v___x_1839_ = v_reuseFailAlloc_1840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_toExprM(
    mut v_pu_1849_: u8,
    mut v_decl_1850_: *mut leanh::LeanObject,
    mut v_a_1851_: *mut leanh::LeanObject,
    mut v_a_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_params_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_params_1853_ = leanh::lean_ctor_get(v_decl_1850_, 2);
    leanh::lean_inc_ref(v_params_1853_);
    v_value_1854_ = leanh::lean_ctor_get(v_decl_1850_, 4);
    leanh::lean_inc_ref(v_value_1854_);
    leanh::lean_dec_ref(v_decl_1850_);
    v___x_1855_ = leanh::lean_unsigned_to_nat(0);
    leanh::lean_inc(v_a_1851_);
    v___x_1856_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_1849_, v_value_1854_, v_params_1853_, v_params_1853_, v___x_1855_, v_a_1851_, v_a_1852_);
    leanh::lean_dec_ref(v_params_1853_);
    return v___x_1856_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_toExprM___boxed(
    mut v_pu_1857_: *mut leanh::LeanObject,
    mut v_decl_1858_: *mut leanh::LeanObject,
    mut v_a_1859_: *mut leanh::LeanObject,
    mut v_a_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1861_: u8 = 0;
    let mut v_res_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1861_ = (leanh::lean_unbox(v_pu_1857_) as u8);
    v_res_1862_ =
        l_Lean_Compiler_LCNF_FunDecl_toExprM(v_pu_boxed_1861_, v_decl_1858_, v_a_1859_, v_a_1860_);
    leanh::lean_dec(v_a_1859_);
    return v_res_1862_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg___boxed(
    mut v_pu_1863_: *mut leanh::LeanObject,
    mut v_value_1864_: *mut leanh::LeanObject,
    mut v_params_1865_: *mut leanh::LeanObject,
    mut v_params_1866_: *mut leanh::LeanObject,
    mut v_i_1867_: *mut leanh::LeanObject,
    mut v_a_1868_: *mut leanh::LeanObject,
    mut v_a_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1870_: u8 = 0;
    let mut v_res_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1870_ = (leanh::lean_unbox(v_pu_1863_) as u8);
    v_res_1871_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_boxed_1870_, v_value_1864_, v_params_1865_, v_params_1866_, v_i_1867_, v_a_1868_, v_a_1869_);
    leanh::lean_dec_ref(v_params_1866_);
    leanh::lean_dec_ref(v_params_1865_);
    return v_res_1871_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3___boxed(
    mut v_pu_1872_: *mut leanh::LeanObject,
    mut v_sz_1873_: *mut leanh::LeanObject,
    mut v_i_1874_: *mut leanh::LeanObject,
    mut v_bs_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1878_: u8 = 0;
    let mut v_sz_boxed_1879_: usize = 0;
    let mut v_i_boxed_1880_: usize = 0;
    let mut v_res_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1878_ = (leanh::lean_unbox(v_pu_1872_) as u8);
    v_sz_boxed_1879_ = leanh::lean_unbox_usize(v_sz_1873_);
    leanh::lean_dec(v_sz_1873_);
    v_i_boxed_1880_ = leanh::lean_unbox_usize(v_i_1874_);
    leanh::lean_dec(v_i_1874_);
    v_res_1881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__3(v_pu_boxed_1878_, v_sz_boxed_1879_, v_i_boxed_1880_, v_bs_1875_, v___y_1876_, v___y_1877_);
    leanh::lean_dec(v___y_1876_);
    return v_res_1881_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_toExprM___boxed(
    mut v_pu_1882_: *mut leanh::LeanObject,
    mut v_code_1883_: *mut leanh::LeanObject,
    mut v_a_1884_: *mut leanh::LeanObject,
    mut v_a_1885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1886_: u8 = 0;
    let mut v_res_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1886_ = (leanh::lean_unbox(v_pu_1882_) as u8);
    v_res_1887_ =
        l_Lean_Compiler_LCNF_Code_toExprM(v_pu_boxed_1886_, v_code_1883_, v_a_1884_, v_a_1885_);
    leanh::lean_dec(v_a_1884_);
    return v_res_1887_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(
    mut v_pu_1888_: u8,
    mut v_value_1889_: *mut leanh::LeanObject,
    mut v_params_1890_: *mut leanh::LeanObject,
    mut v_pu_1891_: u8,
    mut v_params_1892_: *mut leanh::LeanObject,
    mut v_i_1893_: *mut leanh::LeanObject,
    mut v_a_1894_: *mut leanh::LeanObject,
    mut v_a_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1894_);
    v___x_1896_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___redArg(v_pu_1888_, v_value_1889_, v_params_1890_, v_params_1892_, v_i_1893_, v_a_1894_, v_a_1895_);
    return v___x_1896_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0___boxed(
    mut v_pu_1897_: *mut leanh::LeanObject,
    mut v_value_1898_: *mut leanh::LeanObject,
    mut v_params_1899_: *mut leanh::LeanObject,
    mut v_pu_1900_: *mut leanh::LeanObject,
    mut v_params_1901_: *mut leanh::LeanObject,
    mut v_i_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
    mut v_a_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1905_: u8 = 0;
    let mut v_pu_boxed_1906_: u8 = 0;
    let mut v_res_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1905_ = (leanh::lean_unbox(v_pu_1897_) as u8);
    v_pu_boxed_1906_ = (leanh::lean_unbox(v_pu_1900_) as u8);
    v_res_1907_ = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Compiler_LCNF_ToExpr_withParams_go___at___00Lean_Compiler_LCNF_FunDecl_toExprM_spec__0(v_pu_boxed_1905_, v_value_1898_, v_params_1899_, v_pu_boxed_1906_, v_params_1901_, v_i_1902_, v_a_1903_, v_a_1904_);
    leanh::lean_dec(v_a_1903_);
    leanh::lean_dec_ref(v_params_1901_);
    leanh::lean_dec_ref(v_params_1899_);
    return v_res_1907_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(
    mut v_pu_1908_: u8,
    mut v_sz_1909_: usize,
    mut v_i_1910_: usize,
    mut v_bs_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
    mut v___y_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___redArg(v_sz_1909_, v_i_1910_, v_bs_1911_, v___y_1912_, v___y_1913_);
    return v___x_1914_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2___boxed(
    mut v_pu_1915_: *mut leanh::LeanObject,
    mut v_sz_1916_: *mut leanh::LeanObject,
    mut v_i_1917_: *mut leanh::LeanObject,
    mut v_bs_1918_: *mut leanh::LeanObject,
    mut v___y_1919_: *mut leanh::LeanObject,
    mut v___y_1920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1921_: u8 = 0;
    let mut v_sz_boxed_1922_: usize = 0;
    let mut v_i_boxed_1923_: usize = 0;
    let mut v_res_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1921_ = (leanh::lean_unbox(v_pu_1915_) as u8);
    v_sz_boxed_1922_ = leanh::lean_unbox_usize(v_sz_1916_);
    leanh::lean_dec(v_sz_1916_);
    v_i_boxed_1923_ = leanh::lean_unbox_usize(v_i_1917_);
    leanh::lean_dec(v_i_1917_);
    v_res_1924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toExprM_spec__2(v_pu_boxed_1921_, v_sz_boxed_1922_, v_i_boxed_1923_, v_bs_1918_, v___y_1919_, v___y_1920_);
    leanh::lean_dec(v___y_1919_);
    return v_res_1924_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(
    mut v_as_1925_: *mut leanh::LeanObject,
    mut v_i_1926_: usize,
    mut v_stop_1927_: usize,
    mut v_b_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: usize = 0;
    let mut v___x_1932_: usize = 0;
    let mut v___x_1934_: u8 = 0;
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1934_ = lean_usize_dec_eq(v_i_1926_, v_stop_1927_);
                if v___x_1934_ == 0 {
                    v___x_1935_ = lean_array_uget_borrowed(v_as_1925_, v_i_1926_);
                    if leanh::lean_obj_tag(v_b_1928_) == 0 {
                        v_size_1936_ = leanh::lean_ctor_get(v_b_1928_, 0);
                        leanh::lean_inc(v_size_1936_);
                        leanh::lean_inc(v___x_1935_);
                        v___x_1937_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_1935_, v_size_1936_, v_b_1928_);
                        v___y_1930_ = v___x_1937_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1938_ = leanh::lean_unsigned_to_nat(0);
                        leanh::lean_inc(v___x_1935_);
                        v___x_1939_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_1935_, v___x_1938_, v_b_1928_);
                        v___y_1930_ = v___x_1939_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1928_;
                }
            }
            1 => {
                v___x_1931_ = 1usize;
                v___x_1932_ = lean_usize_add(v_i_1926_, v___x_1931_);
                v_i_1926_ = v___x_1932_;
                v_b_1928_ = v___y_1930_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0___boxed(
    mut v_as_1940_: *mut leanh::LeanObject,
    mut v_i_1941_: *mut leanh::LeanObject,
    mut v_stop_1942_: *mut leanh::LeanObject,
    mut v_b_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1944_: usize = 0;
    let mut v_stop_boxed_1945_: usize = 0;
    let mut v_res_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1944_ = leanh::lean_unbox_usize(v_i_1941_);
    leanh::lean_dec(v_i_1941_);
    v_stop_boxed_1945_ = leanh::lean_unbox_usize(v_stop_1942_);
    leanh::lean_dec(v_stop_1942_);
    v_res_1946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_as_1940_, v_i_boxed_1944_, v_stop_boxed_1945_, v_b_1943_);
    leanh::lean_dec_ref(v_as_1940_);
    return v_res_1946_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_toExpr(
    mut v_pu_1947_: u8,
    mut v_code_1948_: *mut leanh::LeanObject,
    mut v_xs_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: u8 = 0;
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: usize = 0;
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: usize = 0;
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1950_ = leanh::lean_box(1);
                v___x_1951_ = leanh::lean_unsigned_to_nat(0);
                v___x_1952_ = lean_array_get_size(v_xs_1949_);
                v___x_1957_ = lean_nat_dec_lt(v___x_1951_, v___x_1952_);
                if v___x_1957_ == 0 {
                    v___y_1954_ = v___x_1950_;
                    state = 1;
                    continue;
                } else {
                    v___x_1958_ = lean_nat_dec_le(v___x_1952_, v___x_1952_);
                    if v___x_1958_ == 0 {
                        if v___x_1957_ == 0 {
                            v___y_1954_ = v___x_1950_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1959_ = 0usize;
                            v___x_1960_ = lean_usize_of_nat(v___x_1952_);
                            v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_1949_, v___x_1959_, v___x_1960_, v___x_1950_);
                            v___y_1954_ = v___x_1961_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1962_ = 0usize;
                        v___x_1963_ = lean_usize_of_nat(v___x_1952_);
                        v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_1949_, v___x_1962_, v___x_1963_, v___x_1950_);
                        v___y_1954_ = v___x_1964_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1955_ = l_Lean_Compiler_LCNF_Code_toExprM(
                    v_pu_1947_,
                    v_code_1948_,
                    v___x_1952_,
                    v___y_1954_,
                );
                v_fst_1956_ = leanh::lean_ctor_get(v___x_1955_, 0);
                leanh::lean_inc(v_fst_1956_);
                leanh::lean_dec_ref(v___x_1955_);
                return v_fst_1956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_toExpr___boxed(
    mut v_pu_1965_: *mut leanh::LeanObject,
    mut v_code_1966_: *mut leanh::LeanObject,
    mut v_xs_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1968_: u8 = 0;
    let mut v_res_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1968_ = (leanh::lean_unbox(v_pu_1965_) as u8);
    v_res_1969_ = l_Lean_Compiler_LCNF_Code_toExpr(v_pu_boxed_1968_, v_code_1966_, v_xs_1967_);
    leanh::lean_dec_ref(v_xs_1967_);
    return v_res_1969_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_toExpr(
    mut v_pu_1970_: u8,
    mut v_decl_1971_: *mut leanh::LeanObject,
    mut v_xs_1972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: usize = 0;
    let mut v___x_1983_: usize = 0;
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: usize = 0;
    let mut v___x_1986_: usize = 0;
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1973_ = leanh::lean_box(1);
                v___x_1974_ = leanh::lean_unsigned_to_nat(0);
                v___x_1975_ = lean_array_get_size(v_xs_1972_);
                v___x_1980_ = lean_nat_dec_lt(v___x_1974_, v___x_1975_);
                if v___x_1980_ == 0 {
                    v___y_1977_ = v___x_1973_;
                    state = 1;
                    continue;
                } else {
                    v___x_1981_ = lean_nat_dec_le(v___x_1975_, v___x_1975_);
                    if v___x_1981_ == 0 {
                        if v___x_1980_ == 0 {
                            v___y_1977_ = v___x_1973_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1982_ = 0usize;
                            v___x_1983_ = lean_usize_of_nat(v___x_1975_);
                            v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_1972_, v___x_1982_, v___x_1983_, v___x_1973_);
                            v___y_1977_ = v___x_1984_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1985_ = 0usize;
                        v___x_1986_ = lean_usize_of_nat(v___x_1975_);
                        v___x_1987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_toExpr_spec__0(v_xs_1972_, v___x_1985_, v___x_1986_, v___x_1973_);
                        v___y_1977_ = v___x_1987_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1978_ = l_Lean_Compiler_LCNF_FunDecl_toExprM(
                    v_pu_1970_,
                    v_decl_1971_,
                    v___x_1975_,
                    v___y_1977_,
                );
                v_fst_1979_ = leanh::lean_ctor_get(v___x_1978_, 0);
                leanh::lean_inc(v_fst_1979_);
                leanh::lean_dec_ref(v___x_1978_);
                return v_fst_1979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_toExpr___boxed(
    mut v_pu_1988_: *mut leanh::LeanObject,
    mut v_decl_1989_: *mut leanh::LeanObject,
    mut v_xs_1990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1991_: u8 = 0;
    let mut v_res_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1991_ = (leanh::lean_unbox(v_pu_1988_) as u8);
    v_res_1992_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(v_pu_boxed_1991_, v_decl_1989_, v_xs_1990_);
    leanh::lean_dec_ref(v_xs_1990_);
    return v_res_1992_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ToExpr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ToExpr(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_ToExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ToExpr(builtin);
}