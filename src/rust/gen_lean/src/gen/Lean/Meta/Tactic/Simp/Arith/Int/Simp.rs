// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: Lean.Meta.Tactic.Simp.Arith.Util Lean.Meta.Tactic.Simp.Arith.Int.Basic
use crate::ffi::{
    lean_array_get_borrowed, lean_expr_eqv, lean_int_dec_eq, lean_int_dec_le, lean_int_ediv,
    lean_int_emod, lean_int_neg, lean_nat_abs, lean_nat_dec_eq, lean_nat_gcd, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Int::Linear::{
    l_Int_Linear_Expr_norm, l_Int_Linear_Poly_div, l_Int_Linear_Poly_gcdCoeffs,
    l_Int_Linear_Poly_getConst, l_Int_Linear_Poly_isUnsatEq, l_Int_Linear_Poly_isUnsatLe,
    l_Int_Linear_Poly_isValidEq, l_Int_Linear_Poly_isValidLe, l_Int_Linear_instBEqExpr_beq,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_isConstOf, l_Lean_eagerReflBoolTrue, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkApp7, l_Lean_mkAppB, l_Lean_mkConst,
    l_Lean_mkIntAdd, l_Lean_mkIntDvd, l_Lean_mkIntEq, l_Lean_mkIntLE, l_Lean_mkIntLit,
    l_Lean_mkNatLit, l_Lean_mkPropEq, l_Lean_mkSort,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_Level_succ___override};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkExpectedPropHint;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Int::Basic::{
    initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic, l_Int_Linear_Expr_denoteExpr___redArg,
    l_Int_Linear_Poly_denoteExpr___redArg, l_Int_Linear_Poly_toExpr,
    l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f, l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f,
    l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f, l_Lean_Meta_Simp_Arith_Int_ofLinearExpr,
    l_Lean_Meta_Simp_Arith_Int_ofPoly, l_Lean_Meta_Simp_Arith_Int_toContextExpr,
    l_Lean_Meta_Simp_Arith_Int_toLinearExpr,
    runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Util::{
    initialize_Lean_Meta_Tactic_Simp_Arith_Util,
    runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util,
};
use crate::r#gen::Lean::ToExpr::l_Lean_instToExprInt_mkNat;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [76, 105, 110, 101, 97, 114, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value: crate::leanh::LeanStringObject<
    18,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        110, 111, 114, 109, 95, 101, 113, 95, 118, 97, 114, 95, 99, 111, 110, 115, 116, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value)
            as *mut crate::leanh::LeanObject,
        10060288092756996131 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [70, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value)
            as *mut crate::leanh::LeanObject,
        907667957179513571 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value: crate::leanh::LeanStringObject<
    24,
> = crate::leanh::LeanStringObject {
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
        101, 113, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 100, 105, 118, 67,
        111, 101, 102, 102, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value)
            as *mut crate::leanh::LeanObject,
        15222022325075373211 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value:
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
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value:
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
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value)
            as *mut crate::leanh::LeanObject,
        9626815015619986526 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value)
            as *mut crate::leanh::LeanObject,
        17185717442815859305 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value)
            as *mut crate::leanh::LeanObject,
        6362876895233142233 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        110, 111, 114, 109, 95, 101, 113, 95, 99, 111, 101, 102, 102, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value)
            as *mut crate::leanh::LeanObject,
        6597761869438004053 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 111, 114, 109, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value)
            as *mut crate::leanh::LeanObject,
        8912318443281423404 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value:
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
    m_data: [110, 111, 114, 109, 95, 101, 113, 95, 118, 97, 114, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value)
            as *mut crate::leanh::LeanObject,
        8314161943217586311 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value:
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
    m_data: [84, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value)
            as *mut crate::leanh::LeanObject,
        11870096045526947150 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [101, 113, 95, 101, 113, 95, 116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value)
            as *mut crate::leanh::LeanObject,
        1301655992456463126 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value:
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
    m_data: [101, 113, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value)
            as *mut crate::leanh::LeanObject,
        397423300456770027 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        110, 111, 114, 109, 95, 108, 101, 95, 99, 111, 101, 102, 102, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10859493989233018008 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value: crate::leanh::LeanStringObject<
    20,
> = crate::leanh::LeanStringObject {
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
        110, 111, 114, 109, 95, 108, 101, 95, 99, 111, 101, 102, 102, 95, 116, 105, 103, 104, 116,
        0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value)
            as *mut crate::leanh::LeanObject,
        14708339156377520116 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 111, 114, 109, 95, 108, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value)
            as *mut crate::leanh::LeanObject,
        1839820918411524584 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value)
            as *mut crate::leanh::LeanObject,
        11529026806789895592 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value:
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
    m_data: [108, 101, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value)
            as *mut crate::leanh::LeanObject,
        9757622324104460876 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [76, 69, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [108, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value)
            as *mut crate::leanh::LeanObject,
        8347582161988589016 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value)
            as *mut crate::leanh::LeanObject,
        7316284823769321069 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value:
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
    m_data: [116, 114, 97, 110, 115, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17532416664988428445 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value:
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
    m_data: [78, 111, 116, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value)
            as *mut crate::leanh::LeanObject,
        16612019923665488825 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [71, 84, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [103, 116, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value)
            as *mut crate::leanh::LeanObject,
        2272833755566510320 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value)
            as *mut crate::leanh::LeanObject,
        9426339939459091439 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [76, 84, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [108, 116, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value)
            as *mut crate::leanh::LeanObject,
        17878876274162330439 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value)
            as *mut crate::leanh::LeanObject,
        11833570877100518198 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [71, 69, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [103, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value)
            as *mut crate::leanh::LeanObject,
        1755019837031360842 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value)
            as *mut crate::leanh::LeanObject,
        5555145617058846791 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 111, 116, 95, 108, 101, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value)
            as *mut crate::leanh::LeanObject,
        5162611250653448781 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 111, 116, 95, 103, 101, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value)
            as *mut crate::leanh::LeanObject,
        330781738820734295 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 111, 116, 95, 108, 116, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value)
            as *mut crate::leanh::LeanObject,
        3394945094387313110 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 111, 116, 95, 103, 116, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value)
            as *mut crate::leanh::LeanObject,
        317193488316801530 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [110, 111, 114, 109, 95, 100, 118, 100, 95, 103, 99, 100, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11199380116660155345 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [110, 111, 114, 109, 95, 100, 118, 100, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3792564684362573326 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [100, 118, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value)
            as *mut crate::leanh::LeanObject,
        13203838950204374860 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value:
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
    m_data: [69, 120, 112, 114, 0],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        101, 113, 95, 111, 102, 95, 110, 111, 114, 109, 95, 101, 113, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10556148748237291170 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        2473476115399171125 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(
    mut v_k_1498_: *mut crate::leanh::LeanObject,
    mut v_p_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: u8 = 0;
    let mut v_k_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1500_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1501_ = lean_nat_dec_eq(v_k_1498_, v___x_1500_);
                if v___x_1501_ == 0 {
                    if crate::leanh::lean_obj_tag(v_p_1499_) == 0 {
                        v_k_1502_ = crate::leanh::lean_ctor_get(v_p_1499_, 0);
                        v___x_1503_ = lean_nat_abs(v_k_1502_);
                        v___x_1504_ = lean_nat_gcd(v_k_1498_, v___x_1503_);
                        crate::leanh::lean_dec(v___x_1503_);
                        crate::leanh::lean_dec(v_k_1498_);
                        return v___x_1504_;
                    } else {
                        v_k_1505_ = crate::leanh::lean_ctor_get(v_p_1499_, 0);
                        v_p_1506_ = crate::leanh::lean_ctor_get(v_p_1499_, 2);
                        v___x_1507_ = lean_nat_abs(v_k_1505_);
                        v___x_1508_ = lean_nat_gcd(v_k_1498_, v___x_1507_);
                        crate::leanh::lean_dec(v___x_1507_);
                        crate::leanh::lean_dec(v_k_1498_);
                        v_k_1498_ = v___x_1508_;
                        v_p_1499_ = v_p_1506_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v_k_1498_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(
    mut v_k_1510_: *mut crate::leanh::LeanObject,
    mut v_p_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1512_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(
        v_k_1510_, v_p_1511_,
    );
    crate::leanh::lean_dec_ref(v_p_1511_);
    return v_res_1512_;
}
pub unsafe fn l_Int_Linear_Poly_gcdAll(
    mut v_x_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1513_) == 0 {
        let mut v_k_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1514_ = crate::leanh::lean_ctor_get(v_x_1513_, 0);
        v___x_1515_ = lean_nat_abs(v_k_1514_);
        return v___x_1515_;
    } else {
        let mut v_k_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1516_ = crate::leanh::lean_ctor_get(v_x_1513_, 0);
        v_p_1517_ = crate::leanh::lean_ctor_get(v_x_1513_, 2);
        v___x_1518_ = lean_nat_abs(v_k_1516_);
        v___x_1519_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(
            v___x_1518_,
            v_p_1517_,
        );
        return v___x_1519_;
    }
}
pub unsafe fn l_Int_Linear_Poly_gcdAll___boxed(
    mut v_x_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1521_ = l_Int_Linear_Poly_gcdAll(v_x_1520_);
    crate::leanh::lean_dec_ref(v_x_1520_);
    return v_res_1521_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(
    mut v_k_1522_: *mut crate::leanh::LeanObject,
    mut v_p_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u8 = 0;
    let mut v_k_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1524_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1525_ = lean_nat_dec_eq(v_k_1522_, v___x_1524_);
                if v___x_1525_ == 0 {
                    if crate::leanh::lean_obj_tag(v_p_1523_) == 0 {
                        return v_k_1522_;
                    } else {
                        v_k_1526_ = crate::leanh::lean_ctor_get(v_p_1523_, 0);
                        v_p_1527_ = crate::leanh::lean_ctor_get(v_p_1523_, 2);
                        v___x_1528_ = lean_nat_abs(v_k_1526_);
                        v___x_1529_ = lean_nat_gcd(v_k_1522_, v___x_1528_);
                        crate::leanh::lean_dec(v___x_1528_);
                        crate::leanh::lean_dec(v_k_1522_);
                        v_k_1522_ = v___x_1529_;
                        v_p_1523_ = v_p_1527_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v_k_1522_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(
    mut v_k_1531_: *mut crate::leanh::LeanObject,
    mut v_p_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1533_ =
        l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(
            v_k_1531_, v_p_1532_,
        );
    crate::leanh::lean_dec_ref(v_p_1532_);
    return v_res_1533_;
}
pub unsafe fn l_Int_Linear_Poly_gcdCoeffs_x27(
    mut v_x_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1534_) == 0 {
        let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1535_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1535_;
    } else {
        let mut v_k_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1536_ = crate::leanh::lean_ctor_get(v_x_1534_, 0);
        v_p_1537_ = crate::leanh::lean_ctor_get(v_x_1534_, 2);
        v___x_1538_ = lean_nat_abs(v_k_1536_);
        v___x_1539_ =
            l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(
                v___x_1538_,
                v_p_1537_,
            );
        return v___x_1539_;
    }
}
pub unsafe fn l_Int_Linear_Poly_gcdCoeffs_x27___boxed(
    mut v_x_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_x_1540_);
    crate::leanh::lean_dec_ref(v_x_1540_);
    return v_res_1541_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(
    mut v_a_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = lean_nat_to_int(v_a_1542_);
    return v___x_1543_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(
    mut v___x_1544_: *mut crate::leanh::LeanObject,
    mut v_snd_1545_: *mut crate::leanh::LeanObject,
    mut v_x_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = lean_array_get_borrowed(v___x_1544_, v_snd_1545_, v_x_1546_);
    crate::leanh::lean_inc(v___x_1547_);
    return v___x_1547_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(
    mut v___x_1548_: *mut crate::leanh::LeanObject,
    mut v_snd_1549_: *mut crate::leanh::LeanObject,
    mut v_x_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1551_ =
        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(v___x_1548_, v_snd_1549_, v_x_1550_);
    crate::leanh::lean_dec(v_x_1550_);
    crate::leanh::lean_dec_ref(v_snd_1549_);
    crate::leanh::lean_dec_ref(v___x_1548_);
    return v_res_1551_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = crate::leanh::lean_box(0);
    v___x_1560_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3;
    v___x_1561_ = l_Lean_mkConst(v___x_1560_, v___x_1559_);
    return v___x_1561_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1563_ = lean_nat_to_int(v___x_1562_);
    return v___x_1563_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1567_ = crate::leanh::lean_box(0);
    v___x_1568_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7;
    v___x_1569_ = l_Lean_mkConst(v___x_1568_, v___x_1567_);
    return v___x_1569_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = crate::leanh::lean_box(0);
    v___x_1576_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10;
    v___x_1577_ = l_Lean_mkConst(v___x_1576_, v___x_1575_);
    return v___x_1577_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1584_ = l_Lean_Level_ofNat(v___x_1583_);
    return v___x_1584_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = crate::leanh::lean_box(0);
    v___x_1586_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15,
    );
    v___x_1587_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1587_, 0, v___x_1586_);
    crate::leanh::lean_ctor_set(v___x_1587_, 1, v___x_1585_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16,
    );
    v___x_1589_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
    v___x_1590_ = l_Lean_Expr_const___override(v___x_1589_, v___x_1588_);
    return v___x_1590_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = crate::leanh::lean_box(0);
    v___x_1594_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
    v___x_1595_ = l_Lean_Expr_const___override(v___x_1594_, v___x_1593_);
    return v___x_1595_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = crate::leanh::lean_box(0);
    v___x_1601_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21;
    v___x_1602_ = l_Lean_Expr_const___override(v___x_1601_, v___x_1600_);
    return v___x_1602_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
    );
    v___x_1604_ = l_Lean_mkIntLit(v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1610_ = crate::leanh::lean_box(0);
    v___x_1611_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25;
    v___x_1612_ = l_Lean_mkConst(v___x_1611_, v___x_1610_);
    return v___x_1612_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ = crate::leanh::lean_box(0);
    v___x_1619_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28;
    v___x_1620_ = l_Lean_mkConst(v___x_1619_, v___x_1618_);
    return v___x_1620_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1622_ = lean_nat_to_int(v___x_1621_);
    return v___x_1622_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30,
    );
    v___x_1624_ = lean_int_neg(v___x_1623_);
    return v___x_1624_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1630_ = crate::leanh::lean_box(0);
    v___x_1631_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33;
    v___x_1632_ = l_Lean_mkConst(v___x_1631_, v___x_1630_);
    return v___x_1632_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1633_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
    );
    v___x_1634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1634_, 0, v___x_1633_);
    return v___x_1634_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = crate::leanh::lean_box(0);
    v___x_1639_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37;
    v___x_1640_ = l_Lean_mkConst(v___x_1639_, v___x_1638_);
    return v___x_1640_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = crate::leanh::lean_box(0);
    v___x_1647_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40;
    v___x_1648_ = l_Lean_mkConst(v___x_1647_, v___x_1646_);
    return v___x_1648_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = crate::leanh::lean_box(0);
    v___x_1655_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43;
    v___x_1656_ = l_Lean_mkConst(v___x_1655_, v___x_1654_);
    return v___x_1656_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(
    mut v_e_1657_: *mut crate::leanh::LeanObject,
    mut v_a_1658_: *mut crate::leanh::LeanObject,
    mut v_a_1659_: *mut crate::leanh::LeanObject,
    mut v_a_1660_: *mut crate::leanh::LeanObject,
    mut v_a_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v_val_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v_snd_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v_fst_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1681_: u8 = 0;
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut v_a_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut v_a_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_a_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut v_a_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v___y_1887_: u8 = 0;
    let mut v_k_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v_k_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v_k_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1926_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut v_a_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1956_: u8 = 0;
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_a_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v_a_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v_a_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2023_: u8 = 0;
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2027_: u8 = 0;
    let mut v_isSharedCheck_2028_: u8 = 0;
    let mut v_a_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_isSharedCheck_2037_: u8 = 0;
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut v_a_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1663_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(
                    v_e_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_,
                );
                if crate::leanh::lean_obj_tag(v___x_1663_) == 0 {
                    v_a_1664_ = crate::leanh::lean_ctor_get(v___x_1663_, 0);
                    v_isSharedCheck_2044_ = (!crate::leanh::lean_is_exclusive(v___x_1663_)) as u8;
                    if v_isSharedCheck_2044_ == 0 {
                        v___x_1666_ = v___x_1663_;
                        v_isShared_1667_ = v_isSharedCheck_2044_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1664_);
                        crate::leanh::lean_dec(v___x_1663_);
                        v___x_1666_ = crate::leanh::lean_box(0);
                        v_isShared_1667_ = v_isSharedCheck_2044_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2045_ = crate::leanh::lean_ctor_get(v___x_1663_, 0);
                    v_isSharedCheck_2052_ = (!crate::leanh::lean_is_exclusive(v___x_1663_)) as u8;
                    if v_isSharedCheck_2052_ == 0 {
                        v___x_2047_ = v___x_1663_;
                        v_isShared_2048_ = v_isSharedCheck_2052_;
                        state = 54;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2045_);
                        crate::leanh::lean_dec(v___x_1663_);
                        v___x_2047_ = crate::leanh::lean_box(0);
                        v_isShared_2048_ = v_isSharedCheck_2052_;
                        state = 54;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1664_) == 1 {
                    v_val_1668_ = crate::leanh::lean_ctor_get(v_a_1664_, 0);
                    v_isSharedCheck_2039_ = (!crate::leanh::lean_is_exclusive(v_a_1664_)) as u8;
                    if v_isSharedCheck_2039_ == 0 {
                        v___x_1670_ = v_a_1664_;
                        v_isShared_1671_ = v_isSharedCheck_2039_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1668_);
                        crate::leanh::lean_dec(v_a_1664_);
                        v___x_1670_ = crate::leanh::lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_2039_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1664_);
                    v___x_2040_ = crate::leanh::lean_box(0);
                    if v_isShared_1667_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1666_, 0, v___x_2040_);
                        v___x_2042_ = v___x_1666_;
                        state = 53;
                        continue;
                    } else {
                        v_reuseFailAlloc_2043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
                        v___x_2042_ = v_reuseFailAlloc_2043_;
                        state = 53;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_1672_ = crate::leanh::lean_ctor_get(v_val_1668_, 1);
                v_fst_1673_ = crate::leanh::lean_ctor_get(v_val_1668_, 0);
                v_isSharedCheck_2038_ = (!crate::leanh::lean_is_exclusive(v_val_1668_)) as u8;
                if v_isSharedCheck_2038_ == 0 {
                    v___x_1675_ = v_val_1668_;
                    v_isShared_1676_ = v_isSharedCheck_2038_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1672_);
                    crate::leanh::lean_inc(v_fst_1673_);
                    crate::leanh::lean_dec(v_val_1668_);
                    v___x_1675_ = crate::leanh::lean_box(0);
                    v_isShared_1676_ = v_isSharedCheck_2038_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_1677_ = crate::leanh::lean_ctor_get(v_snd_1672_, 0);
                v_snd_1678_ = crate::leanh::lean_ctor_get(v_snd_1672_, 1);
                v_isSharedCheck_2037_ = (!crate::leanh::lean_is_exclusive(v_snd_1672_)) as u8;
                if v_isSharedCheck_2037_ == 0 {
                    v___x_1680_ = v_snd_1672_;
                    v_isShared_1681_ = v_isSharedCheck_2037_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1678_);
                    crate::leanh::lean_inc(v_fst_1677_);
                    crate::leanh::lean_dec(v_snd_1672_);
                    v___x_1680_ = crate::leanh::lean_box(0);
                    v_isShared_1681_ = v_isSharedCheck_2037_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1682_ = l_Lean_instInhabitedExpr;
                crate::leanh::lean_inc(v_snd_1678_);
                v___f_1683_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1683_, 0, v___x_1682_);
                crate::leanh::lean_closure_set(v___f_1683_, 1, v_snd_1678_);
                crate::leanh::lean_inc(v_fst_1673_);
                crate::leanh::lean_inc_ref(v___f_1683_);
                v___x_1684_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_1683_, v_fst_1673_);
                if crate::leanh::lean_obj_tag(v___x_1684_) == 0 {
                    v_a_1685_ = crate::leanh::lean_ctor_get(v___x_1684_, 0);
                    v_isSharedCheck_2028_ = (!crate::leanh::lean_is_exclusive(v___x_1684_)) as u8;
                    if v_isSharedCheck_2028_ == 0 {
                        v___x_1687_ = v___x_1684_;
                        v_isShared_1688_ = v_isSharedCheck_2028_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1685_);
                        crate::leanh::lean_dec(v___x_1684_);
                        v___x_1687_ = crate::leanh::lean_box(0);
                        v_isShared_1688_ = v_isSharedCheck_2028_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_1683_);
                    crate::leanh::lean_del_object(v___x_1680_);
                    crate::leanh::lean_dec(v_snd_1678_);
                    crate::leanh::lean_dec(v_fst_1677_);
                    crate::leanh::lean_del_object(v___x_1675_);
                    crate::leanh::lean_dec(v_fst_1673_);
                    crate::leanh::lean_del_object(v___x_1670_);
                    crate::leanh::lean_del_object(v___x_1666_);
                    v_a_2029_ = crate::leanh::lean_ctor_get(v___x_1684_, 0);
                    v_isSharedCheck_2036_ = (!crate::leanh::lean_is_exclusive(v___x_1684_)) as u8;
                    if v_isSharedCheck_2036_ == 0 {
                        v___x_2031_ = v___x_1684_;
                        v_isShared_2032_ = v_isSharedCheck_2036_;
                        state = 51;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2029_);
                        crate::leanh::lean_dec(v___x_1684_);
                        v___x_2031_ = crate::leanh::lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2036_;
                        state = 51;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_fst_1677_);
                crate::leanh::lean_inc_ref(v___f_1683_);
                v___x_1689_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_1683_, v_fst_1677_);
                if crate::leanh::lean_obj_tag(v___x_1689_) == 0 {
                    v_a_1690_ = crate::leanh::lean_ctor_get(v___x_1689_, 0);
                    v_isSharedCheck_2019_ = (!crate::leanh::lean_is_exclusive(v___x_1689_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_1692_ = v___x_1689_;
                        v_isShared_1693_ = v_isSharedCheck_2019_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1690_);
                        crate::leanh::lean_dec(v___x_1689_);
                        v___x_1692_ = crate::leanh::lean_box(0);
                        v_isShared_1693_ = v_isSharedCheck_2019_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1687_);
                    crate::leanh::lean_dec(v_a_1685_);
                    crate::leanh::lean_dec_ref(v___f_1683_);
                    crate::leanh::lean_del_object(v___x_1680_);
                    crate::leanh::lean_dec(v_snd_1678_);
                    crate::leanh::lean_dec(v_fst_1677_);
                    crate::leanh::lean_del_object(v___x_1675_);
                    crate::leanh::lean_dec(v_fst_1673_);
                    crate::leanh::lean_del_object(v___x_1670_);
                    crate::leanh::lean_del_object(v___x_1666_);
                    v_a_2020_ = crate::leanh::lean_ctor_get(v___x_1689_, 0);
                    v_isSharedCheck_2027_ = (!crate::leanh::lean_is_exclusive(v___x_1689_)) as u8;
                    if v_isSharedCheck_2027_ == 0 {
                        v___x_2022_ = v___x_1689_;
                        v_isShared_2023_ = v_isSharedCheck_2027_;
                        state = 49;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2020_);
                        crate::leanh::lean_dec(v___x_1689_);
                        v___x_2022_ = crate::leanh::lean_box(0);
                        v_isShared_2023_ = v_isSharedCheck_2027_;
                        state = 49;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1694_ = l_Lean_mkIntEq(v_a_1685_, v_a_1690_);
                crate::leanh::lean_inc(v_fst_1677_);
                crate::leanh::lean_inc(v_fst_1673_);
                v___x_1771_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1771_, 0, v_fst_1673_);
                crate::leanh::lean_ctor_set(v___x_1771_, 1, v_fst_1677_);
                v___x_1772_ = l_Int_Linear_Expr_norm(v___x_1771_);
                crate::leanh::lean_dec_ref_known(v___x_1771_, 2);
                v___x_1959_ = l_Int_Linear_Poly_isUnsatEq(v___x_1772_);
                if v___x_1959_ == 0 {
                    v___x_1960_ = l_Int_Linear_Poly_isValidEq(v___x_1772_);
                    if v___x_1960_ == 0 {
                        crate::leanh::lean_inc_ref(v___x_1772_);
                        v___x_1961_ = l_Int_Linear_Poly_toExpr(v___x_1772_);
                        v___x_1962_ = l_Int_Linear_instBEqExpr_beq(v___x_1961_, v_fst_1673_);
                        crate::leanh::lean_dec_ref(v___x_1961_);
                        if v___x_1962_ == 0 {
                            v___y_1887_ = v___x_1962_;
                            state = 33;
                            continue;
                        } else {
                            v___x_1963_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35,
                            );
                            v___x_1964_ = l_Int_Linear_instBEqExpr_beq(v_fst_1677_, v___x_1963_);
                            v___y_1887_ = v___x_1964_;
                            state = 33;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1772_);
                        crate::leanh::lean_del_object(v___x_1692_);
                        crate::leanh::lean_del_object(v___x_1687_);
                        crate::leanh::lean_dec_ref(v___f_1683_);
                        crate::leanh::lean_del_object(v___x_1680_);
                        crate::leanh::lean_del_object(v___x_1675_);
                        crate::leanh::lean_del_object(v___x_1670_);
                        crate::leanh::lean_del_object(v___x_1666_);
                        v___x_1965_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v_snd_1678_,
                            v_a_1658_,
                            v_a_1659_,
                            v_a_1660_,
                            v_a_1661_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1965_) == 0 {
                            v_a_1966_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                            v_isSharedCheck_1983_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1965_)) as u8;
                            if v_isSharedCheck_1983_ == 0 {
                                v___x_1968_ = v___x_1965_;
                                v_isShared_1969_ = v_isSharedCheck_1983_;
                                state = 41;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1966_);
                                crate::leanh::lean_dec(v___x_1965_);
                                v___x_1968_ = crate::leanh::lean_box(0);
                                v_isShared_1969_ = v_isSharedCheck_1983_;
                                state = 41;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1694_);
                            crate::leanh::lean_dec(v_fst_1677_);
                            crate::leanh::lean_dec(v_fst_1673_);
                            v_a_1984_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                            v_isSharedCheck_1991_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1965_)) as u8;
                            if v_isSharedCheck_1991_ == 0 {
                                v___x_1986_ = v___x_1965_;
                                v_isShared_1987_ = v_isSharedCheck_1991_;
                                state = 43;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1984_);
                                crate::leanh::lean_dec(v___x_1965_);
                                v___x_1986_ = crate::leanh::lean_box(0);
                                v_isShared_1987_ = v_isSharedCheck_1991_;
                                state = 43;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1772_);
                    crate::leanh::lean_del_object(v___x_1692_);
                    crate::leanh::lean_del_object(v___x_1687_);
                    crate::leanh::lean_dec_ref(v___f_1683_);
                    crate::leanh::lean_del_object(v___x_1680_);
                    crate::leanh::lean_del_object(v___x_1675_);
                    crate::leanh::lean_del_object(v___x_1670_);
                    crate::leanh::lean_del_object(v___x_1666_);
                    v___x_1992_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_1678_,
                        v_a_1658_,
                        v_a_1659_,
                        v_a_1660_,
                        v_a_1661_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1992_) == 0 {
                        v_a_1993_ = crate::leanh::lean_ctor_get(v___x_1992_, 0);
                        v_isSharedCheck_2010_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1992_)) as u8;
                        if v_isSharedCheck_2010_ == 0 {
                            v___x_1995_ = v___x_1992_;
                            v_isShared_1996_ = v_isSharedCheck_2010_;
                            state = 45;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1993_);
                            crate::leanh::lean_dec(v___x_1992_);
                            v___x_1995_ = crate::leanh::lean_box(0);
                            v_isShared_1996_ = v_isSharedCheck_2010_;
                            state = 45;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1694_);
                        crate::leanh::lean_dec(v_fst_1677_);
                        crate::leanh::lean_dec(v_fst_1673_);
                        v_a_2011_ = crate::leanh::lean_ctor_get(v___x_1992_, 0);
                        v_isSharedCheck_2018_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1992_)) as u8;
                        if v_isSharedCheck_2018_ == 0 {
                            v___x_2013_ = v___x_1992_;
                            v_isShared_2014_ = v_isSharedCheck_2018_;
                            state = 47;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2011_);
                            crate::leanh::lean_dec(v___x_1992_);
                            v___x_2013_ = crate::leanh::lean_box(0);
                            v_isShared_2014_ = v_isSharedCheck_2018_;
                            state = 47;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_1702_ = l_Lean_eagerReflBoolTrue;
                crate::leanh::lean_inc_ref(v___y_1697_);
                v___x_1703_ = l_Lean_mkApp5(
                    v___y_1697_,
                    v___y_1696_,
                    v___y_1699_,
                    v___y_1700_,
                    v___y_1701_,
                    v___x_1702_,
                );
                crate::leanh::lean_inc_ref_n(v___y_1698_, 2);
                v___x_1704_ = l_Lean_mkPropEq(v___x_1694_, v___y_1698_);
                v___x_1705_ = l_Lean_Meta_mkExpectedPropHint(v___x_1703_, v___x_1704_);
                if v_isShared_1681_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1680_, 1, v___x_1705_);
                    crate::leanh::lean_ctor_set(v___x_1680_, 0, v___y_1698_);
                    v___x_1707_ = v___x_1680_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___y_1698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1705_);
                    v___x_1707_ = v_reuseFailAlloc_1714_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1671_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1670_, 0, v___x_1707_);
                    v___x_1709_ = v___x_1670_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1707_);
                    v___x_1709_ = v_reuseFailAlloc_1713_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1693_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1692_, 0, v___x_1709_);
                    v___x_1711_ = v___x_1692_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
                    v___x_1711_ = v_reuseFailAlloc_1712_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1711_;
            }
            11 => {
                v___x_1723_ = l_Lean_eagerReflBoolTrue;
                crate::leanh::lean_inc_ref(v___y_1719_);
                v___x_1724_ = l_Lean_mkApp6(
                    v___y_1719_,
                    v___y_1717_,
                    v___y_1718_,
                    v___y_1716_,
                    v___y_1721_,
                    v___y_1722_,
                    v___x_1723_,
                );
                crate::leanh::lean_inc_ref(v___y_1720_);
                v___x_1725_ = l_Lean_mkPropEq(v___x_1694_, v___y_1720_);
                v___x_1726_ = l_Lean_Meta_mkExpectedPropHint(v___x_1724_, v___x_1725_);
                if v_isShared_1676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1675_, 1, v___x_1726_);
                    crate::leanh::lean_ctor_set(v___x_1675_, 0, v___y_1720_);
                    v___x_1728_ = v___x_1675_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1733_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___y_1720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1726_);
                    v___x_1728_ = v_reuseFailAlloc_1733_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1729_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1729_, 0, v___x_1728_);
                if v_isShared_1688_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1687_, 0, v___x_1729_);
                    v___x_1731_ = v___x_1687_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
                    v___x_1731_ = v_reuseFailAlloc_1732_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1731_;
            }
            14 => {
                crate::leanh::lean_inc_ref(v___y_1737_);
                v___x_1738_ = l_Lean_mkIntEq(v___y_1735_, v___y_1737_);
                v___x_1739_ = lean_expr_eqv(v___x_1738_, v___x_1694_);
                if v___x_1739_ == 0 {
                    crate::leanh::lean_del_object(v___x_1666_);
                    v___x_1740_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_1678_,
                        v_a_1658_,
                        v_a_1659_,
                        v_a_1660_,
                        v_a_1661_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1740_) == 0 {
                        v_a_1741_ = crate::leanh::lean_ctor_get(v___x_1740_, 0);
                        v_isSharedCheck_1758_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1758_ == 0 {
                            v___x_1743_ = v___x_1740_;
                            v_isShared_1744_ = v_isSharedCheck_1758_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1741_);
                            crate::leanh::lean_dec(v___x_1740_);
                            v___x_1743_ = crate::leanh::lean_box(0);
                            v_isShared_1744_ = v_isSharedCheck_1758_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1738_);
                        crate::leanh::lean_dec_ref(v___y_1737_);
                        crate::leanh::lean_dec(v___y_1736_);
                        crate::leanh::lean_dec_ref(v___x_1694_);
                        crate::leanh::lean_dec(v_fst_1677_);
                        crate::leanh::lean_dec(v_fst_1673_);
                        v_a_1759_ = crate::leanh::lean_ctor_get(v___x_1740_, 0);
                        v_isSharedCheck_1766_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1766_ == 0 {
                            v___x_1761_ = v___x_1740_;
                            v_isShared_1762_ = v_isSharedCheck_1766_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1759_);
                            crate::leanh::lean_dec(v___x_1740_);
                            v___x_1761_ = crate::leanh::lean_box(0);
                            v_isShared_1762_ = v_isSharedCheck_1766_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1738_);
                    crate::leanh::lean_dec_ref(v___y_1737_);
                    crate::leanh::lean_dec(v___y_1736_);
                    crate::leanh::lean_dec_ref(v___x_1694_);
                    crate::leanh::lean_dec(v_snd_1678_);
                    crate::leanh::lean_dec(v_fst_1677_);
                    crate::leanh::lean_dec(v_fst_1673_);
                    v___x_1767_ = crate::leanh::lean_box(0);
                    if v_isShared_1667_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1666_, 0, v___x_1767_);
                        v___x_1769_ = v___x_1666_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_1770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
                        v___x_1769_ = v_reuseFailAlloc_1770_;
                        state = 19;
                        continue;
                    }
                }
            }
            15 => {
                v___x_1745_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4,
                );
                v___x_1746_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1673_);
                v___x_1747_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1677_);
                v___x_1748_ = l_Lean_mkNatLit(v___y_1736_);
                v___x_1749_ = l_Lean_eagerReflBoolTrue;
                v___x_1750_ = l_Lean_mkApp6(
                    v___x_1745_,
                    v_a_1741_,
                    v___x_1746_,
                    v___x_1747_,
                    v___x_1748_,
                    v___y_1737_,
                    v___x_1749_,
                );
                crate::leanh::lean_inc_ref(v___x_1738_);
                v___x_1751_ = l_Lean_mkPropEq(v___x_1694_, v___x_1738_);
                v___x_1752_ = l_Lean_Meta_mkExpectedPropHint(v___x_1750_, v___x_1751_);
                v___x_1753_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1738_);
                crate::leanh::lean_ctor_set(v___x_1753_, 1, v___x_1752_);
                v___x_1754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1754_, 0, v___x_1753_);
                if v_isShared_1744_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1754_);
                    v___x_1756_ = v___x_1743_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
                    v___x_1756_ = v_reuseFailAlloc_1757_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1756_;
            }
            17 => {
                if v_isShared_1762_ == 0 {
                    v___x_1764_ = v___x_1761_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
                    v___x_1764_ = v_reuseFailAlloc_1765_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1764_;
            }
            19 => {
                return v___x_1769_;
            }
            20 => {
                v___x_1778_ = l_Int_Linear_Poly_gcdCoeffs_x27(v___x_1772_);
                v___x_1779_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1780_ = lean_nat_dec_eq(v___x_1778_, v___x_1779_);
                if v___x_1780_ == 0 {
                    v___x_1781_ = l_Int_Linear_Poly_getConst(v___x_1772_);
                    v___x_1782_ = lean_nat_to_int(v___x_1778_);
                    v___x_1783_ = lean_int_emod(v___x_1781_, v___x_1782_);
                    crate::leanh::lean_dec(v___x_1781_);
                    v___x_1784_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
                    );
                    v___x_1785_ = lean_int_dec_eq(v___x_1783_, v___x_1784_);
                    crate::leanh::lean_dec(v___x_1783_);
                    if v___x_1785_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1772_);
                        crate::leanh::lean_del_object(v___x_1687_);
                        crate::leanh::lean_dec_ref(v___f_1683_);
                        crate::leanh::lean_del_object(v___x_1675_);
                        v___x_1786_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v_snd_1678_,
                            v___y_1774_,
                            v___y_1775_,
                            v___y_1776_,
                            v___y_1777_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1786_) == 0 {
                            v_a_1787_ = crate::leanh::lean_ctor_get(v___x_1786_, 0);
                            crate::leanh::lean_inc(v_a_1787_);
                            crate::leanh::lean_dec_ref_known(v___x_1786_, 1);
                            v___x_1788_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8,
                            );
                            v___x_1789_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11,
                            );
                            v___x_1790_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1673_);
                            v___x_1791_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1677_);
                            v___x_1792_ = lean_int_dec_le(v___x_1784_, v___x_1782_);
                            if v___x_1792_ == 0 {
                                v___x_1793_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                                );
                                v___x_1794_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                );
                                v___x_1795_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                );
                                v___x_1796_ = lean_int_neg(v___x_1782_);
                                crate::leanh::lean_dec(v___x_1782_);
                                v___x_1797_ = l_Int_toNat(v___x_1796_);
                                crate::leanh::lean_dec(v___x_1796_);
                                v___x_1798_ = l_Lean_instToExprInt_mkNat(v___x_1797_);
                                v___x_1799_ = l_Lean_mkApp3(
                                    v___x_1793_,
                                    v___x_1794_,
                                    v___x_1795_,
                                    v___x_1798_,
                                );
                                v___y_1696_ = v_a_1787_;
                                v___y_1697_ = v___x_1789_;
                                v___y_1698_ = v___x_1788_;
                                v___y_1699_ = v___x_1790_;
                                v___y_1700_ = v___x_1791_;
                                v___y_1701_ = v___x_1799_;
                                state = 7;
                                continue;
                            } else {
                                v___x_1800_ = l_Int_toNat(v___x_1782_);
                                crate::leanh::lean_dec(v___x_1782_);
                                v___x_1801_ = l_Lean_instToExprInt_mkNat(v___x_1800_);
                                v___y_1696_ = v_a_1787_;
                                v___y_1697_ = v___x_1789_;
                                v___y_1698_ = v___x_1788_;
                                v___y_1699_ = v___x_1790_;
                                v___y_1700_ = v___x_1791_;
                                v___y_1701_ = v___x_1801_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1782_);
                            crate::leanh::lean_dec_ref(v___x_1694_);
                            crate::leanh::lean_del_object(v___x_1692_);
                            crate::leanh::lean_del_object(v___x_1680_);
                            crate::leanh::lean_dec(v_fst_1677_);
                            crate::leanh::lean_dec(v_fst_1673_);
                            crate::leanh::lean_del_object(v___x_1670_);
                            v_a_1802_ = crate::leanh::lean_ctor_get(v___x_1786_, 0);
                            v_isSharedCheck_1809_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1786_)) as u8;
                            if v_isSharedCheck_1809_ == 0 {
                                v___x_1804_ = v___x_1786_;
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1802_);
                                crate::leanh::lean_dec(v___x_1786_);
                                v___x_1804_ = crate::leanh::lean_box(0);
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1692_);
                        crate::leanh::lean_del_object(v___x_1680_);
                        crate::leanh::lean_del_object(v___x_1670_);
                        v___x_1810_ = l_Int_Linear_Poly_div(v___x_1782_, v___x_1772_);
                        crate::leanh::lean_inc_ref(v___x_1810_);
                        v___x_1811_ =
                            l_Int_Linear_Poly_denoteExpr___redArg(v___f_1683_, v___x_1810_);
                        if crate::leanh::lean_obj_tag(v___x_1811_) == 0 {
                            v_a_1812_ = crate::leanh::lean_ctor_get(v___x_1811_, 0);
                            crate::leanh::lean_inc(v_a_1812_);
                            crate::leanh::lean_dec_ref_known(v___x_1811_, 1);
                            v___x_1813_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                                v_snd_1678_,
                                v___y_1774_,
                                v___y_1775_,
                                v___y_1776_,
                                v___y_1777_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1813_) == 0 {
                                v_a_1814_ = crate::leanh::lean_ctor_get(v___x_1813_, 0);
                                crate::leanh::lean_inc(v_a_1814_);
                                crate::leanh::lean_dec_ref_known(v___x_1813_, 1);
                                v___x_1815_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23,
                                );
                                v___x_1816_ = l_Lean_mkIntEq(v_a_1812_, v___x_1815_);
                                v___x_1817_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26,
                                );
                                v___x_1818_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1673_);
                                v___x_1819_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1677_);
                                v___x_1820_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_1810_);
                                v___x_1821_ = lean_int_dec_le(v___x_1784_, v___x_1782_);
                                if v___x_1821_ == 0 {
                                    v___x_1822_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                                    );
                                    v___x_1823_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                    );
                                    v___x_1824_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                    );
                                    v___x_1825_ = lean_int_neg(v___x_1782_);
                                    crate::leanh::lean_dec(v___x_1782_);
                                    v___x_1826_ = l_Int_toNat(v___x_1825_);
                                    crate::leanh::lean_dec(v___x_1825_);
                                    v___x_1827_ = l_Lean_instToExprInt_mkNat(v___x_1826_);
                                    v___x_1828_ = l_Lean_mkApp3(
                                        v___x_1822_,
                                        v___x_1823_,
                                        v___x_1824_,
                                        v___x_1827_,
                                    );
                                    v___y_1716_ = v___x_1819_;
                                    v___y_1717_ = v_a_1814_;
                                    v___y_1718_ = v___x_1818_;
                                    v___y_1719_ = v___x_1817_;
                                    v___y_1720_ = v___x_1816_;
                                    v___y_1721_ = v___x_1820_;
                                    v___y_1722_ = v___x_1828_;
                                    state = 11;
                                    continue;
                                } else {
                                    v___x_1829_ = l_Int_toNat(v___x_1782_);
                                    crate::leanh::lean_dec(v___x_1782_);
                                    v___x_1830_ = l_Lean_instToExprInt_mkNat(v___x_1829_);
                                    v___y_1716_ = v___x_1819_;
                                    v___y_1717_ = v_a_1814_;
                                    v___y_1718_ = v___x_1818_;
                                    v___y_1719_ = v___x_1817_;
                                    v___y_1720_ = v___x_1816_;
                                    v___y_1721_ = v___x_1820_;
                                    v___y_1722_ = v___x_1830_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1812_);
                                crate::leanh::lean_dec_ref(v___x_1810_);
                                crate::leanh::lean_dec(v___x_1782_);
                                crate::leanh::lean_dec_ref(v___x_1694_);
                                crate::leanh::lean_del_object(v___x_1687_);
                                crate::leanh::lean_dec(v_fst_1677_);
                                crate::leanh::lean_del_object(v___x_1675_);
                                crate::leanh::lean_dec(v_fst_1673_);
                                v_a_1831_ = crate::leanh::lean_ctor_get(v___x_1813_, 0);
                                v_isSharedCheck_1838_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1813_)) as u8;
                                if v_isSharedCheck_1838_ == 0 {
                                    v___x_1833_ = v___x_1813_;
                                    v_isShared_1834_ = v_isSharedCheck_1838_;
                                    state = 23;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1831_);
                                    crate::leanh::lean_dec(v___x_1813_);
                                    v___x_1833_ = crate::leanh::lean_box(0);
                                    v_isShared_1834_ = v_isSharedCheck_1838_;
                                    state = 23;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1810_);
                            crate::leanh::lean_dec(v___x_1782_);
                            crate::leanh::lean_dec_ref(v___x_1694_);
                            crate::leanh::lean_del_object(v___x_1687_);
                            crate::leanh::lean_dec(v_snd_1678_);
                            crate::leanh::lean_dec(v_fst_1677_);
                            crate::leanh::lean_del_object(v___x_1675_);
                            crate::leanh::lean_dec(v_fst_1673_);
                            v_a_1839_ = crate::leanh::lean_ctor_get(v___x_1811_, 0);
                            v_isSharedCheck_1846_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1811_)) as u8;
                            if v_isSharedCheck_1846_ == 0 {
                                v___x_1841_ = v___x_1811_;
                                v_isShared_1842_ = v_isSharedCheck_1846_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1839_);
                                crate::leanh::lean_dec(v___x_1811_);
                                v___x_1841_ = crate::leanh::lean_box(0);
                                v_isShared_1842_ = v_isSharedCheck_1846_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1778_);
                    crate::leanh::lean_del_object(v___x_1692_);
                    crate::leanh::lean_del_object(v___x_1687_);
                    crate::leanh::lean_del_object(v___x_1680_);
                    crate::leanh::lean_del_object(v___x_1675_);
                    crate::leanh::lean_del_object(v___x_1670_);
                    crate::leanh::lean_inc_ref(v___x_1772_);
                    v___x_1847_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_1683_, v___x_1772_);
                    if crate::leanh::lean_obj_tag(v___x_1847_) == 0 {
                        v_a_1848_ = crate::leanh::lean_ctor_get(v___x_1847_, 0);
                        crate::leanh::lean_inc(v_a_1848_);
                        crate::leanh::lean_dec_ref_known(v___x_1847_, 1);
                        v___x_1849_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v_snd_1678_,
                            v___y_1774_,
                            v___y_1775_,
                            v___y_1776_,
                            v___y_1777_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1849_) == 0 {
                            v_a_1850_ = crate::leanh::lean_ctor_get(v___x_1849_, 0);
                            v_isSharedCheck_1869_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1849_)) as u8;
                            if v_isSharedCheck_1869_ == 0 {
                                v___x_1852_ = v___x_1849_;
                                v_isShared_1853_ = v_isSharedCheck_1869_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1850_);
                                crate::leanh::lean_dec(v___x_1849_);
                                v___x_1852_ = crate::leanh::lean_box(0);
                                v_isShared_1853_ = v_isSharedCheck_1869_;
                                state = 27;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1848_);
                            crate::leanh::lean_dec_ref(v___x_1772_);
                            crate::leanh::lean_dec_ref(v___x_1694_);
                            crate::leanh::lean_dec(v_fst_1677_);
                            crate::leanh::lean_dec(v_fst_1673_);
                            v_a_1870_ = crate::leanh::lean_ctor_get(v___x_1849_, 0);
                            v_isSharedCheck_1877_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1849_)) as u8;
                            if v_isSharedCheck_1877_ == 0 {
                                v___x_1872_ = v___x_1849_;
                                v_isShared_1873_ = v_isSharedCheck_1877_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1870_);
                                crate::leanh::lean_dec(v___x_1849_);
                                v___x_1872_ = crate::leanh::lean_box(0);
                                v_isShared_1873_ = v_isSharedCheck_1877_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1772_);
                        crate::leanh::lean_dec_ref(v___x_1694_);
                        crate::leanh::lean_dec(v_snd_1678_);
                        crate::leanh::lean_dec(v_fst_1677_);
                        crate::leanh::lean_dec(v_fst_1673_);
                        v_a_1878_ = crate::leanh::lean_ctor_get(v___x_1847_, 0);
                        v_isSharedCheck_1885_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1847_)) as u8;
                        if v_isSharedCheck_1885_ == 0 {
                            v___x_1880_ = v___x_1847_;
                            v_isShared_1881_ = v_isSharedCheck_1885_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1878_);
                            crate::leanh::lean_dec(v___x_1847_);
                            v___x_1880_ = crate::leanh::lean_box(0);
                            v_isShared_1881_ = v_isSharedCheck_1885_;
                            state = 31;
                            continue;
                        }
                    }
                }
            }
            21 => {
                if v_isShared_1805_ == 0 {
                    v___x_1807_ = v___x_1804_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
                    v___x_1807_ = v_reuseFailAlloc_1808_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1807_;
            }
            23 => {
                if v_isShared_1834_ == 0 {
                    v___x_1836_ = v___x_1833_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
                    v___x_1836_ = v_reuseFailAlloc_1837_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1836_;
            }
            25 => {
                if v_isShared_1842_ == 0 {
                    v___x_1844_ = v___x_1841_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
                    v___x_1844_ = v_reuseFailAlloc_1845_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1844_;
            }
            27 => {
                v___x_1854_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23,
                );
                v___x_1855_ = l_Lean_mkIntEq(v_a_1848_, v___x_1854_);
                v___x_1856_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29,
                );
                v___x_1857_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1673_);
                v___x_1858_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1677_);
                v___x_1859_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_1772_);
                v___x_1860_ = l_Lean_eagerReflBoolTrue;
                v___x_1861_ = l_Lean_mkApp5(
                    v___x_1856_,
                    v_a_1850_,
                    v___x_1857_,
                    v___x_1858_,
                    v___x_1859_,
                    v___x_1860_,
                );
                crate::leanh::lean_inc_ref(v___x_1855_);
                v___x_1862_ = l_Lean_mkPropEq(v___x_1694_, v___x_1855_);
                v___x_1863_ = l_Lean_Meta_mkExpectedPropHint(v___x_1861_, v___x_1862_);
                v___x_1864_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1855_);
                crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1863_);
                v___x_1865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1865_, 0, v___x_1864_);
                if v_isShared_1853_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1852_, 0, v___x_1865_);
                    v___x_1867_ = v___x_1852_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
                    v___x_1867_ = v_reuseFailAlloc_1868_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1867_;
            }
            29 => {
                if v_isShared_1873_ == 0 {
                    v___x_1875_ = v___x_1872_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1876_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
                    v___x_1875_ = v_reuseFailAlloc_1876_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_1875_;
            }
            31 => {
                if v_isShared_1881_ == 0 {
                    v___x_1883_ = v___x_1880_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
                    v___x_1883_ = v_reuseFailAlloc_1884_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1883_;
            }
            33 => {
                if v___y_1887_ == 0 {
                    if crate::leanh::lean_obj_tag(v___x_1772_) == 1 {
                        v_k_1888_ = crate::leanh::lean_ctor_get(v___x_1772_, 0);
                        crate::leanh::lean_inc(v_k_1888_);
                        v_v_1889_ = crate::leanh::lean_ctor_get(v___x_1772_, 1);
                        crate::leanh::lean_inc(v_v_1889_);
                        v_p_1890_ = crate::leanh::lean_ctor_get(v___x_1772_, 2);
                        crate::leanh::lean_inc_ref(v_p_1890_);
                        v___x_1891_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30,
                        );
                        v___x_1892_ = lean_int_dec_eq(v_k_1888_, v___x_1891_);
                        crate::leanh::lean_dec(v_k_1888_);
                        if v___x_1892_ == 0 {
                            crate::leanh::lean_dec_ref(v_p_1890_);
                            crate::leanh::lean_dec(v_v_1889_);
                            crate::leanh::lean_del_object(v___x_1666_);
                            v___y_1774_ = v_a_1658_;
                            v___y_1775_ = v_a_1659_;
                            v___y_1776_ = v_a_1660_;
                            v___y_1777_ = v_a_1661_;
                            state = 20;
                            continue;
                        } else {
                            if crate::leanh::lean_obj_tag(v_p_1890_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1772_, 3);
                                crate::leanh::lean_del_object(v___x_1692_);
                                crate::leanh::lean_del_object(v___x_1687_);
                                crate::leanh::lean_dec_ref(v___f_1683_);
                                crate::leanh::lean_del_object(v___x_1680_);
                                crate::leanh::lean_del_object(v___x_1675_);
                                crate::leanh::lean_del_object(v___x_1670_);
                                v_k_1893_ = crate::leanh::lean_ctor_get(v_p_1890_, 0);
                                crate::leanh::lean_inc(v_k_1893_);
                                crate::leanh::lean_dec_ref_known(v_p_1890_, 1);
                                v___x_1894_ =
                                    lean_array_get_borrowed(v___x_1682_, v_snd_1678_, v_v_1889_);
                                v___x_1895_ = lean_int_neg(v_k_1893_);
                                crate::leanh::lean_dec(v_k_1893_);
                                v___x_1896_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
                                );
                                v___x_1897_ = lean_int_dec_le(v___x_1896_, v___x_1895_);
                                if v___x_1897_ == 0 {
                                    v___x_1898_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                                    );
                                    v___x_1899_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                    );
                                    v___x_1900_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                    );
                                    v___x_1901_ = lean_int_neg(v___x_1895_);
                                    crate::leanh::lean_dec(v___x_1895_);
                                    v___x_1902_ = l_Int_toNat(v___x_1901_);
                                    crate::leanh::lean_dec(v___x_1901_);
                                    v___x_1903_ = l_Lean_instToExprInt_mkNat(v___x_1902_);
                                    v___x_1904_ = l_Lean_mkApp3(
                                        v___x_1898_,
                                        v___x_1899_,
                                        v___x_1900_,
                                        v___x_1903_,
                                    );
                                    crate::leanh::lean_inc(v___x_1894_);
                                    v___y_1735_ = v___x_1894_;
                                    v___y_1736_ = v_v_1889_;
                                    v___y_1737_ = v___x_1904_;
                                    state = 14;
                                    continue;
                                } else {
                                    v___x_1905_ = l_Int_toNat(v___x_1895_);
                                    crate::leanh::lean_dec(v___x_1895_);
                                    v___x_1906_ = l_Lean_instToExprInt_mkNat(v___x_1905_);
                                    crate::leanh::lean_inc(v___x_1894_);
                                    v___y_1735_ = v___x_1894_;
                                    v___y_1736_ = v_v_1889_;
                                    v___y_1737_ = v___x_1906_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_1666_);
                                v_k_1907_ = crate::leanh::lean_ctor_get(v_p_1890_, 0);
                                crate::leanh::lean_inc(v_k_1907_);
                                v_v_1908_ = crate::leanh::lean_ctor_get(v_p_1890_, 1);
                                crate::leanh::lean_inc(v_v_1908_);
                                v_p_1909_ = crate::leanh::lean_ctor_get(v_p_1890_, 2);
                                crate::leanh::lean_inc_ref(v_p_1909_);
                                crate::leanh::lean_dec_ref_known(v_p_1890_, 3);
                                v___x_1910_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31,
                                );
                                v___x_1911_ = lean_int_dec_eq(v_k_1907_, v___x_1910_);
                                crate::leanh::lean_dec(v_k_1907_);
                                if v___x_1911_ == 0 {
                                    crate::leanh::lean_dec_ref(v_p_1909_);
                                    crate::leanh::lean_dec(v_v_1908_);
                                    crate::leanh::lean_dec(v_v_1889_);
                                    v___y_1774_ = v_a_1658_;
                                    v___y_1775_ = v_a_1659_;
                                    v___y_1776_ = v_a_1660_;
                                    v___y_1777_ = v_a_1661_;
                                    state = 20;
                                    continue;
                                } else {
                                    if crate::leanh::lean_obj_tag(v_p_1909_) == 0 {
                                        v_k_1912_ = crate::leanh::lean_ctor_get(v_p_1909_, 0);
                                        v_isSharedCheck_1956_ =
                                            (!crate::leanh::lean_is_exclusive(v_p_1909_)) as u8;
                                        if v_isSharedCheck_1956_ == 0 {
                                            v___x_1914_ = v_p_1909_;
                                            v_isShared_1915_ = v_isSharedCheck_1956_;
                                            state = 34;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_k_1912_);
                                            crate::leanh::lean_dec(v_p_1909_);
                                            v___x_1914_ = crate::leanh::lean_box(0);
                                            v_isShared_1915_ = v_isSharedCheck_1956_;
                                            state = 34;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_p_1909_);
                                        crate::leanh::lean_dec(v_v_1908_);
                                        crate::leanh::lean_dec(v_v_1889_);
                                        v___y_1774_ = v_a_1658_;
                                        v___y_1775_ = v_a_1659_;
                                        v___y_1776_ = v_a_1660_;
                                        v___y_1777_ = v_a_1661_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1666_);
                        v___y_1774_ = v_a_1658_;
                        v___y_1775_ = v_a_1659_;
                        v___y_1776_ = v_a_1660_;
                        v___y_1777_ = v_a_1661_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1772_);
                    crate::leanh::lean_dec_ref(v___x_1694_);
                    crate::leanh::lean_del_object(v___x_1692_);
                    crate::leanh::lean_del_object(v___x_1687_);
                    crate::leanh::lean_dec_ref(v___f_1683_);
                    crate::leanh::lean_del_object(v___x_1680_);
                    crate::leanh::lean_dec(v_snd_1678_);
                    crate::leanh::lean_dec(v_fst_1677_);
                    crate::leanh::lean_del_object(v___x_1675_);
                    crate::leanh::lean_dec(v_fst_1673_);
                    crate::leanh::lean_del_object(v___x_1670_);
                    crate::leanh::lean_del_object(v___x_1666_);
                    v___x_1957_ = crate::leanh::lean_box(0);
                    v___x_1958_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1958_, 0, v___x_1957_);
                    return v___x_1958_;
                }
            }
            34 => {
                v___x_1916_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
                );
                v___x_1917_ = lean_int_dec_eq(v_k_1912_, v___x_1916_);
                crate::leanh::lean_dec(v_k_1912_);
                if v___x_1917_ == 0 {
                    crate::leanh::lean_del_object(v___x_1914_);
                    crate::leanh::lean_dec(v_v_1908_);
                    crate::leanh::lean_dec(v_v_1889_);
                    v___y_1774_ = v_a_1658_;
                    v___y_1775_ = v_a_1659_;
                    v___y_1776_ = v_a_1660_;
                    v___y_1777_ = v_a_1661_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1772_, 3);
                    crate::leanh::lean_del_object(v___x_1692_);
                    crate::leanh::lean_del_object(v___x_1687_);
                    crate::leanh::lean_dec_ref(v___f_1683_);
                    crate::leanh::lean_del_object(v___x_1680_);
                    crate::leanh::lean_del_object(v___x_1675_);
                    crate::leanh::lean_del_object(v___x_1670_);
                    v___x_1918_ = lean_array_get_borrowed(v___x_1682_, v_snd_1678_, v_v_1889_);
                    v___x_1919_ = lean_array_get_borrowed(v___x_1682_, v_snd_1678_, v_v_1908_);
                    crate::leanh::lean_inc(v___x_1919_);
                    crate::leanh::lean_inc(v___x_1918_);
                    v___x_1920_ = l_Lean_mkIntEq(v___x_1918_, v___x_1919_);
                    v___x_1921_ = lean_expr_eqv(v___x_1920_, v___x_1694_);
                    if v___x_1921_ == 0 {
                        v___x_1922_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v_snd_1678_,
                            v_a_1658_,
                            v_a_1659_,
                            v_a_1660_,
                            v_a_1661_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1922_) == 0 {
                            v_a_1923_ = crate::leanh::lean_ctor_get(v___x_1922_, 0);
                            v_isSharedCheck_1943_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1922_)) as u8;
                            if v_isSharedCheck_1943_ == 0 {
                                v___x_1925_ = v___x_1922_;
                                v_isShared_1926_ = v_isSharedCheck_1943_;
                                state = 35;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1923_);
                                crate::leanh::lean_dec(v___x_1922_);
                                v___x_1925_ = crate::leanh::lean_box(0);
                                v_isShared_1926_ = v_isSharedCheck_1943_;
                                state = 35;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1920_);
                            crate::leanh::lean_del_object(v___x_1914_);
                            crate::leanh::lean_dec(v_v_1908_);
                            crate::leanh::lean_dec(v_v_1889_);
                            crate::leanh::lean_dec_ref(v___x_1694_);
                            crate::leanh::lean_dec(v_fst_1677_);
                            crate::leanh::lean_dec(v_fst_1673_);
                            v_a_1944_ = crate::leanh::lean_ctor_get(v___x_1922_, 0);
                            v_isSharedCheck_1951_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1922_)) as u8;
                            if v_isSharedCheck_1951_ == 0 {
                                v___x_1946_ = v___x_1922_;
                                v_isShared_1947_ = v_isSharedCheck_1951_;
                                state = 38;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1944_);
                                crate::leanh::lean_dec(v___x_1922_);
                                v___x_1946_ = crate::leanh::lean_box(0);
                                v_isShared_1947_ = v_isSharedCheck_1951_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1920_);
                        crate::leanh::lean_dec(v_v_1908_);
                        crate::leanh::lean_dec(v_v_1889_);
                        crate::leanh::lean_dec_ref(v___x_1694_);
                        crate::leanh::lean_dec(v_snd_1678_);
                        crate::leanh::lean_dec(v_fst_1677_);
                        crate::leanh::lean_dec(v_fst_1673_);
                        v___x_1952_ = crate::leanh::lean_box(0);
                        if v_isShared_1915_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1952_);
                            v___x_1954_ = v___x_1914_;
                            state = 40;
                            continue;
                        } else {
                            v_reuseFailAlloc_1955_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
                            v___x_1954_ = v_reuseFailAlloc_1955_;
                            state = 40;
                            continue;
                        }
                    }
                }
            }
            35 => {
                v___x_1927_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34,
                );
                v___x_1928_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1673_);
                v___x_1929_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1677_);
                v___x_1930_ = l_Lean_mkNatLit(v_v_1889_);
                v___x_1931_ = l_Lean_mkNatLit(v_v_1908_);
                v___x_1932_ = l_Lean_eagerReflBoolTrue;
                v___x_1933_ = l_Lean_mkApp6(
                    v___x_1927_,
                    v_a_1923_,
                    v___x_1928_,
                    v___x_1929_,
                    v___x_1930_,
                    v___x_1931_,
                    v___x_1932_,
                );
                crate::leanh::lean_inc_ref(v___x_1920_);
                v___x_1934_ = l_Lean_mkPropEq(v___x_1694_, v___x_1920_);
                v___x_1935_ = l_Lean_Meta_mkExpectedPropHint(v___x_1933_, v___x_1934_);
                v___x_1936_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_1920_);
                crate::leanh::lean_ctor_set(v___x_1936_, 1, v___x_1935_);
                if v_isShared_1915_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1914_, 1);
                    crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1936_);
                    v___x_1938_ = v___x_1914_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1936_);
                    v___x_1938_ = v_reuseFailAlloc_1942_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_1926_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1925_, 0, v___x_1938_);
                    v___x_1940_ = v___x_1925_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
                    v___x_1940_ = v_reuseFailAlloc_1941_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1940_;
            }
            38 => {
                if v_isShared_1947_ == 0 {
                    v___x_1949_ = v___x_1946_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
                    v___x_1949_ = v_reuseFailAlloc_1950_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_1949_;
            }
            40 => {
                return v___x_1954_;
            }
            41 => {
                v___x_1970_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38,
                );
                v___x_1971_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41,
                );
                v___x_1972_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1673_);
                v___x_1973_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1677_);
                v___x_1974_ = l_Lean_eagerReflBoolTrue;
                v___x_1975_ = l_Lean_mkApp4(
                    v___x_1971_,
                    v_a_1966_,
                    v___x_1972_,
                    v___x_1973_,
                    v___x_1974_,
                );
                v___x_1976_ = l_Lean_mkPropEq(v___x_1694_, v___x_1970_);
                v___x_1977_ = l_Lean_Meta_mkExpectedPropHint(v___x_1975_, v___x_1976_);
                v___x_1978_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1978_, 0, v___x_1970_);
                crate::leanh::lean_ctor_set(v___x_1978_, 1, v___x_1977_);
                v___x_1979_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1979_, 0, v___x_1978_);
                if v_isShared_1969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1968_, 0, v___x_1979_);
                    v___x_1981_ = v___x_1968_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
                    v___x_1981_ = v_reuseFailAlloc_1982_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_1981_;
            }
            43 => {
                if v_isShared_1987_ == 0 {
                    v___x_1989_ = v___x_1986_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
                    v___x_1989_ = v_reuseFailAlloc_1990_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_1989_;
            }
            45 => {
                v___x_1997_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8,
                );
                v___x_1998_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44,
                );
                v___x_1999_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1673_);
                v___x_2000_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1677_);
                v___x_2001_ = l_Lean_eagerReflBoolTrue;
                v___x_2002_ = l_Lean_mkApp4(
                    v___x_1998_,
                    v_a_1993_,
                    v___x_1999_,
                    v___x_2000_,
                    v___x_2001_,
                );
                v___x_2003_ = l_Lean_mkPropEq(v___x_1694_, v___x_1997_);
                v___x_2004_ = l_Lean_Meta_mkExpectedPropHint(v___x_2002_, v___x_2003_);
                v___x_2005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2005_, 0, v___x_1997_);
                crate::leanh::lean_ctor_set(v___x_2005_, 1, v___x_2004_);
                v___x_2006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2006_, 0, v___x_2005_);
                if v_isShared_1996_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1995_, 0, v___x_2006_);
                    v___x_2008_ = v___x_1995_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
                    v___x_2008_ = v_reuseFailAlloc_2009_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2008_;
            }
            47 => {
                if v_isShared_2014_ == 0 {
                    v___x_2016_ = v___x_2013_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2017_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
                    v___x_2016_ = v_reuseFailAlloc_2017_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2016_;
            }
            49 => {
                if v_isShared_2023_ == 0 {
                    v___x_2025_ = v___x_2022_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2026_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
                    v___x_2025_ = v_reuseFailAlloc_2026_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_2025_;
            }
            51 => {
                if v_isShared_2032_ == 0 {
                    v___x_2034_ = v___x_2031_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
                    v___x_2034_ = v_reuseFailAlloc_2035_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_2034_;
            }
            53 => {
                return v___x_2042_;
            }
            54 => {
                if v_isShared_2048_ == 0 {
                    v___x_2050_ = v___x_2047_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_2051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
                    v___x_2050_ = v_reuseFailAlloc_2051_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_2050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(
    mut v_e_2053_: *mut crate::leanh::LeanObject,
    mut v_a_2054_: *mut crate::leanh::LeanObject,
    mut v_a_2055_: *mut crate::leanh::LeanObject,
    mut v_a_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v_a_2058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2059_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(
        v_e_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_,
    );
    crate::leanh::lean_dec(v_a_2057_);
    crate::leanh::lean_dec_ref(v_a_2056_);
    crate::leanh::lean_dec(v_a_2055_);
    crate::leanh::lean_dec_ref(v_a_2054_);
    return v_res_2059_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = crate::leanh::lean_box(0);
    v___x_2066_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1;
    v___x_2067_ = l_Lean_mkConst(v___x_2066_, v___x_2065_);
    return v___x_2067_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2073_ = crate::leanh::lean_box(0);
    v___x_2074_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4;
    v___x_2075_ = l_Lean_mkConst(v___x_2074_, v___x_2073_);
    return v___x_2075_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2081_ = crate::leanh::lean_box(0);
    v___x_2082_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7;
    v___x_2083_ = l_Lean_mkConst(v___x_2082_, v___x_2081_);
    return v___x_2083_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = crate::leanh::lean_box(0);
    v___x_2090_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10;
    v___x_2091_ = l_Lean_mkConst(v___x_2090_, v___x_2089_);
    return v___x_2091_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2097_ = crate::leanh::lean_box(0);
    v___x_2098_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13;
    v___x_2099_ = l_Lean_mkConst(v___x_2098_, v___x_2097_);
    return v___x_2099_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(
    mut v_e_2105_: *mut crate::leanh::LeanObject,
    mut v_checkIfModified_2106_: u8,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
    mut v_a_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: u8 = 0;
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2214_: u8 = 0;
    let mut v_a_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut v___y_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v_a_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v_a_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2281_: u8 = 0;
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2286_: u8 = 0;
    let mut v_val_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v_snd_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v_fst_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___f_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2345_: u8 = 0;
    let mut v_a_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2353_: u8 = 0;
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut v_a_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2384_: u8 = 0;
    let mut v_reuseFailAlloc_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2386_: u8 = 0;
    let mut v_a_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_a_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2398_: u8 = 0;
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2402_: u8 = 0;
    let mut v_isSharedCheck_2403_: u8 = 0;
    let mut v_isSharedCheck_2404_: u8 = 0;
    let mut v_isSharedCheck_2405_: u8 = 0;
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_a_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2418_: u8 = 0;
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2279_ = l_Lean_instInhabitedExpr;
                v___x_2419_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17;
                v___x_2420_ = l_Lean_Expr_isAppOf(v_e_2105_, v___x_2419_);
                if v___x_2420_ == 0 {
                    v___y_2281_ = v___x_2420_;
                    state = 18;
                    continue;
                } else {
                    v___y_2281_ = v_checkIfModified_2106_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2113_);
                v___x_2116_ = l_Lean_mkPropEq(v___y_2114_, v___y_2113_);
                v___x_2117_ = l_Lean_Meta_mkExpectedPropHint(v_h_2115_, v___x_2116_);
                v___x_2118_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2118_, 0, v___y_2113_);
                crate::leanh::lean_ctor_set(v___x_2118_, 1, v___x_2117_);
                v___x_2119_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2119_, 0, v___x_2118_);
                v___x_2120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2120_, 0, v___x_2119_);
                return v___x_2120_;
            }
            2 => {
                v___x_2130_ = l_Lean_eagerReflBoolTrue;
                crate::leanh::lean_inc_ref(v___y_2125_);
                v___x_2131_ = l_Lean_mkApp6(
                    v___y_2125_,
                    v___y_2128_,
                    v___y_2127_,
                    v___y_2123_,
                    v___y_2122_,
                    v___y_2129_,
                    v___x_2130_,
                );
                v___y_2113_ = v___y_2124_;
                v___y_2114_ = v___y_2126_;
                v_h_2115_ = v___x_2131_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2141_ = l_Lean_eagerReflBoolTrue;
                crate::leanh::lean_inc_ref(v___y_2133_);
                v___x_2142_ = l_Lean_mkApp6(
                    v___y_2133_,
                    v___y_2138_,
                    v___y_2135_,
                    v___y_2137_,
                    v___y_2136_,
                    v___y_2140_,
                    v___x_2141_,
                );
                v___y_2113_ = v___y_2134_;
                v___y_2114_ = v___y_2139_;
                v_h_2115_ = v___x_2142_;
                state = 1;
                continue;
            }
            4 => {
                v___x_2154_ = l_Int_Linear_Poly_div(v___y_2145_, v___y_2147_);
                crate::leanh::lean_inc_ref(v___x_2154_);
                v___x_2155_ = l_Int_Linear_Poly_denoteExpr___redArg(v___y_2151_, v___x_2154_);
                if crate::leanh::lean_obj_tag(v___x_2155_) == 0 {
                    v_a_2156_ = crate::leanh::lean_ctor_get(v___x_2155_, 0);
                    crate::leanh::lean_inc(v_a_2156_);
                    crate::leanh::lean_dec_ref_known(v___x_2155_, 1);
                    v___x_2157_ = l_Lean_mkIntLit(v___y_2144_);
                    v___x_2158_ = l_Lean_mkIntLE(v_a_2156_, v___x_2157_);
                    if v___y_2153_ == 0 {
                        v___x_2159_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v___y_2150_,
                            v_a_2107_,
                            v_a_2108_,
                            v_a_2109_,
                            v_a_2110_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2159_) == 0 {
                            v_a_2160_ = crate::leanh::lean_ctor_get(v___x_2159_, 0);
                            crate::leanh::lean_inc(v_a_2160_);
                            crate::leanh::lean_dec_ref_known(v___x_2159_, 1);
                            v___x_2161_ = crate::leanh::lean_box(0);
                            v___x_2162_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2,
                            );
                            v___x_2163_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_2149_);
                            v___x_2164_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_2146_);
                            v___x_2165_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_2154_);
                            v___x_2166_ = lean_int_dec_le(v___y_2144_, v___y_2145_);
                            if v___x_2166_ == 0 {
                                v___x_2167_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
                                v___x_2168_ = l_Lean_Level_ofNat(v___y_2148_);
                                v___x_2169_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2169_, 0, v___x_2168_);
                                crate::leanh::lean_ctor_set(v___x_2169_, 1, v___x_2161_);
                                v___x_2170_ =
                                    l_Lean_Expr_const___override(v___x_2167_, v___x_2169_);
                                v___x_2171_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                );
                                v___x_2172_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                );
                                v___x_2173_ = lean_int_neg(v___y_2145_);
                                crate::leanh::lean_dec(v___y_2145_);
                                v___x_2174_ = l_Int_toNat(v___x_2173_);
                                crate::leanh::lean_dec(v___x_2173_);
                                v___x_2175_ = l_Lean_instToExprInt_mkNat(v___x_2174_);
                                v___x_2176_ = l_Lean_mkApp3(
                                    v___x_2170_,
                                    v___x_2171_,
                                    v___x_2172_,
                                    v___x_2175_,
                                );
                                v___y_2133_ = v___x_2162_;
                                v___y_2134_ = v___x_2158_;
                                v___y_2135_ = v___x_2163_;
                                v___y_2136_ = v___x_2165_;
                                v___y_2137_ = v___x_2164_;
                                v___y_2138_ = v_a_2160_;
                                v___y_2139_ = v___y_2152_;
                                v___y_2140_ = v___x_2176_;
                                state = 3;
                                continue;
                            } else {
                                v___x_2177_ = l_Int_toNat(v___y_2145_);
                                crate::leanh::lean_dec(v___y_2145_);
                                v___x_2178_ = l_Lean_instToExprInt_mkNat(v___x_2177_);
                                v___y_2133_ = v___x_2162_;
                                v___y_2134_ = v___x_2158_;
                                v___y_2135_ = v___x_2163_;
                                v___y_2136_ = v___x_2165_;
                                v___y_2137_ = v___x_2164_;
                                v___y_2138_ = v_a_2160_;
                                v___y_2139_ = v___y_2152_;
                                v___y_2140_ = v___x_2178_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2158_);
                            crate::leanh::lean_dec_ref(v___x_2154_);
                            crate::leanh::lean_dec_ref(v___y_2152_);
                            crate::leanh::lean_dec_ref(v___y_2149_);
                            crate::leanh::lean_dec_ref(v___y_2146_);
                            crate::leanh::lean_dec(v___y_2145_);
                            v_a_2179_ = crate::leanh::lean_ctor_get(v___x_2159_, 0);
                            v_isSharedCheck_2186_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2159_)) as u8;
                            if v_isSharedCheck_2186_ == 0 {
                                v___x_2181_ = v___x_2159_;
                                v_isShared_2182_ = v_isSharedCheck_2186_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2179_);
                                crate::leanh::lean_dec(v___x_2159_);
                                v___x_2181_ = crate::leanh::lean_box(0);
                                v_isShared_2182_ = v_isSharedCheck_2186_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___x_2187_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v___y_2150_,
                            v_a_2107_,
                            v_a_2108_,
                            v_a_2109_,
                            v_a_2110_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2187_) == 0 {
                            v_a_2188_ = crate::leanh::lean_ctor_get(v___x_2187_, 0);
                            crate::leanh::lean_inc(v_a_2188_);
                            crate::leanh::lean_dec_ref_known(v___x_2187_, 1);
                            v___x_2189_ = crate::leanh::lean_box(0);
                            v___x_2190_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5,
                            );
                            v___x_2191_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_2149_);
                            v___x_2192_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_2146_);
                            v___x_2193_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_2154_);
                            v___x_2194_ = lean_int_dec_le(v___y_2144_, v___y_2145_);
                            if v___x_2194_ == 0 {
                                v___x_2195_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
                                v___x_2196_ = l_Lean_Level_ofNat(v___y_2148_);
                                v___x_2197_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2197_, 0, v___x_2196_);
                                crate::leanh::lean_ctor_set(v___x_2197_, 1, v___x_2189_);
                                v___x_2198_ =
                                    l_Lean_Expr_const___override(v___x_2195_, v___x_2197_);
                                v___x_2199_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                );
                                v___x_2200_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                );
                                v___x_2201_ = lean_int_neg(v___y_2145_);
                                crate::leanh::lean_dec(v___y_2145_);
                                v___x_2202_ = l_Int_toNat(v___x_2201_);
                                crate::leanh::lean_dec(v___x_2201_);
                                v___x_2203_ = l_Lean_instToExprInt_mkNat(v___x_2202_);
                                v___x_2204_ = l_Lean_mkApp3(
                                    v___x_2198_,
                                    v___x_2199_,
                                    v___x_2200_,
                                    v___x_2203_,
                                );
                                v___y_2122_ = v___x_2193_;
                                v___y_2123_ = v___x_2192_;
                                v___y_2124_ = v___x_2158_;
                                v___y_2125_ = v___x_2190_;
                                v___y_2126_ = v___y_2152_;
                                v___y_2127_ = v___x_2191_;
                                v___y_2128_ = v_a_2188_;
                                v___y_2129_ = v___x_2204_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2205_ = l_Int_toNat(v___y_2145_);
                                crate::leanh::lean_dec(v___y_2145_);
                                v___x_2206_ = l_Lean_instToExprInt_mkNat(v___x_2205_);
                                v___y_2122_ = v___x_2193_;
                                v___y_2123_ = v___x_2192_;
                                v___y_2124_ = v___x_2158_;
                                v___y_2125_ = v___x_2190_;
                                v___y_2126_ = v___y_2152_;
                                v___y_2127_ = v___x_2191_;
                                v___y_2128_ = v_a_2188_;
                                v___y_2129_ = v___x_2206_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2158_);
                            crate::leanh::lean_dec_ref(v___x_2154_);
                            crate::leanh::lean_dec_ref(v___y_2152_);
                            crate::leanh::lean_dec_ref(v___y_2149_);
                            crate::leanh::lean_dec_ref(v___y_2146_);
                            crate::leanh::lean_dec(v___y_2145_);
                            v_a_2207_ = crate::leanh::lean_ctor_get(v___x_2187_, 0);
                            v_isSharedCheck_2214_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2187_)) as u8;
                            if v_isSharedCheck_2214_ == 0 {
                                v___x_2209_ = v___x_2187_;
                                v_isShared_2210_ = v_isSharedCheck_2214_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2207_);
                                crate::leanh::lean_dec(v___x_2187_);
                                v___x_2209_ = crate::leanh::lean_box(0);
                                v_isShared_2210_ = v_isSharedCheck_2214_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2154_);
                    crate::leanh::lean_dec_ref(v___y_2152_);
                    crate::leanh::lean_dec_ref(v___y_2150_);
                    crate::leanh::lean_dec_ref(v___y_2149_);
                    crate::leanh::lean_dec_ref(v___y_2146_);
                    crate::leanh::lean_dec(v___y_2145_);
                    v_a_2215_ = crate::leanh::lean_ctor_get(v___x_2155_, 0);
                    v_isSharedCheck_2222_ = (!crate::leanh::lean_is_exclusive(v___x_2155_)) as u8;
                    if v_isSharedCheck_2222_ == 0 {
                        v___x_2217_ = v___x_2155_;
                        v_isShared_2218_ = v_isSharedCheck_2222_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2215_);
                        crate::leanh::lean_dec(v___x_2155_);
                        v___x_2217_ = crate::leanh::lean_box(0);
                        v_isShared_2218_ = v_isSharedCheck_2222_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_2182_ == 0 {
                    v___x_2184_ = v___x_2181_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2184_;
            }
            7 => {
                if v_isShared_2210_ == 0 {
                    v___x_2212_ = v___x_2209_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
                    v___x_2212_ = v_reuseFailAlloc_2213_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2212_;
            }
            9 => {
                if v_isShared_2218_ == 0 {
                    v___x_2220_ = v___x_2217_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
                    v___x_2220_ = v_reuseFailAlloc_2221_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2220_;
            }
            11 => {
                v___x_2230_ = l_Int_Linear_Poly_gcdCoeffs_x27(v___y_2225_);
                v___x_2231_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2232_ = lean_nat_dec_eq(v___x_2230_, v___x_2231_);
                if v___x_2232_ == 0 {
                    v___x_2233_ = l_Int_Linear_Poly_getConst(v___y_2225_);
                    v___x_2234_ = lean_nat_to_int(v___x_2230_);
                    v___x_2235_ = lean_int_emod(v___x_2233_, v___x_2234_);
                    crate::leanh::lean_dec(v___x_2233_);
                    v___x_2236_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2237_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
                    );
                    v___x_2238_ = lean_int_dec_eq(v___x_2235_, v___x_2237_);
                    crate::leanh::lean_dec(v___x_2235_);
                    if v___x_2238_ == 0 {
                        v___x_2239_ = 1;
                        v___y_2144_ = v___x_2237_;
                        v___y_2145_ = v___x_2234_;
                        v___y_2146_ = v___y_2224_;
                        v___y_2147_ = v___y_2225_;
                        v___y_2148_ = v___x_2236_;
                        v___y_2149_ = v___y_2226_;
                        v___y_2150_ = v___y_2227_;
                        v___y_2151_ = v___y_2228_;
                        v___y_2152_ = v___y_2229_;
                        v___y_2153_ = v___x_2239_;
                        state = 4;
                        continue;
                    } else {
                        v___y_2144_ = v___x_2237_;
                        v___y_2145_ = v___x_2234_;
                        v___y_2146_ = v___y_2224_;
                        v___y_2147_ = v___y_2225_;
                        v___y_2148_ = v___x_2236_;
                        v___y_2149_ = v___y_2226_;
                        v___y_2150_ = v___y_2227_;
                        v___y_2151_ = v___y_2228_;
                        v___y_2152_ = v___y_2229_;
                        v___y_2153_ = v___x_2232_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2230_);
                    crate::leanh::lean_inc_ref(v___y_2225_);
                    v___x_2240_ = l_Int_Linear_Poly_denoteExpr___redArg(v___y_2228_, v___y_2225_);
                    if crate::leanh::lean_obj_tag(v___x_2240_) == 0 {
                        v_a_2241_ = crate::leanh::lean_ctor_get(v___x_2240_, 0);
                        crate::leanh::lean_inc(v_a_2241_);
                        crate::leanh::lean_dec_ref_known(v___x_2240_, 1);
                        v___x_2242_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v___y_2227_,
                            v_a_2107_,
                            v_a_2108_,
                            v_a_2109_,
                            v_a_2110_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2242_) == 0 {
                            v_a_2243_ = crate::leanh::lean_ctor_get(v___x_2242_, 0);
                            v_isSharedCheck_2262_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2242_)) as u8;
                            if v_isSharedCheck_2262_ == 0 {
                                v___x_2245_ = v___x_2242_;
                                v_isShared_2246_ = v_isSharedCheck_2262_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2243_);
                                crate::leanh::lean_dec(v___x_2242_);
                                v___x_2245_ = crate::leanh::lean_box(0);
                                v_isShared_2246_ = v_isSharedCheck_2262_;
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2241_);
                            crate::leanh::lean_dec_ref(v___y_2229_);
                            crate::leanh::lean_dec_ref(v___y_2226_);
                            crate::leanh::lean_dec_ref(v___y_2225_);
                            crate::leanh::lean_dec_ref(v___y_2224_);
                            v_a_2263_ = crate::leanh::lean_ctor_get(v___x_2242_, 0);
                            v_isSharedCheck_2270_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2242_)) as u8;
                            if v_isSharedCheck_2270_ == 0 {
                                v___x_2265_ = v___x_2242_;
                                v_isShared_2266_ = v_isSharedCheck_2270_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2263_);
                                crate::leanh::lean_dec(v___x_2242_);
                                v___x_2265_ = crate::leanh::lean_box(0);
                                v_isShared_2266_ = v_isSharedCheck_2270_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_2229_);
                        crate::leanh::lean_dec_ref(v___y_2227_);
                        crate::leanh::lean_dec_ref(v___y_2226_);
                        crate::leanh::lean_dec_ref(v___y_2225_);
                        crate::leanh::lean_dec_ref(v___y_2224_);
                        v_a_2271_ = crate::leanh::lean_ctor_get(v___x_2240_, 0);
                        v_isSharedCheck_2278_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2240_)) as u8;
                        if v_isSharedCheck_2278_ == 0 {
                            v___x_2273_ = v___x_2240_;
                            v_isShared_2274_ = v_isSharedCheck_2278_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2271_);
                            crate::leanh::lean_dec(v___x_2240_);
                            v___x_2273_ = crate::leanh::lean_box(0);
                            v_isShared_2274_ = v_isSharedCheck_2278_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___x_2247_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23,
                );
                v___x_2248_ = l_Lean_mkIntLE(v_a_2241_, v___x_2247_);
                v___x_2249_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8,
                );
                v___x_2250_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_2226_);
                v___x_2251_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_2224_);
                v___x_2252_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_2225_);
                v___x_2253_ = l_Lean_eagerReflBoolTrue;
                v___x_2254_ = l_Lean_mkApp5(
                    v___x_2249_,
                    v_a_2243_,
                    v___x_2250_,
                    v___x_2251_,
                    v___x_2252_,
                    v___x_2253_,
                );
                crate::leanh::lean_inc_ref(v___x_2248_);
                v___x_2255_ = l_Lean_mkPropEq(v___y_2229_, v___x_2248_);
                v___x_2256_ = l_Lean_Meta_mkExpectedPropHint(v___x_2254_, v___x_2255_);
                v___x_2257_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2248_);
                crate::leanh::lean_ctor_set(v___x_2257_, 1, v___x_2256_);
                v___x_2258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2258_, 0, v___x_2257_);
                if v_isShared_2246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2258_);
                    v___x_2260_ = v___x_2245_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
                    v___x_2260_ = v_reuseFailAlloc_2261_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2260_;
            }
            14 => {
                if v_isShared_2266_ == 0 {
                    v___x_2268_ = v___x_2265_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2268_;
            }
            16 => {
                if v_isShared_2274_ == 0 {
                    v___x_2276_ = v___x_2273_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2277_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2276_;
            }
            18 => {
                v___x_2282_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(
                    v_e_2105_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_,
                );
                if crate::leanh::lean_obj_tag(v___x_2282_) == 0 {
                    v_a_2283_ = crate::leanh::lean_ctor_get(v___x_2282_, 0);
                    v_isSharedCheck_2410_ = (!crate::leanh::lean_is_exclusive(v___x_2282_)) as u8;
                    if v_isSharedCheck_2410_ == 0 {
                        v___x_2285_ = v___x_2282_;
                        v_isShared_2286_ = v_isSharedCheck_2410_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2283_);
                        crate::leanh::lean_dec(v___x_2282_);
                        v___x_2285_ = crate::leanh::lean_box(0);
                        v_isShared_2286_ = v_isSharedCheck_2410_;
                        state = 19;
                        continue;
                    }
                } else {
                    v_a_2411_ = crate::leanh::lean_ctor_get(v___x_2282_, 0);
                    v_isSharedCheck_2418_ = (!crate::leanh::lean_is_exclusive(v___x_2282_)) as u8;
                    if v_isSharedCheck_2418_ == 0 {
                        v___x_2413_ = v___x_2282_;
                        v_isShared_2414_ = v_isSharedCheck_2418_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2411_);
                        crate::leanh::lean_dec(v___x_2282_);
                        v___x_2413_ = crate::leanh::lean_box(0);
                        v_isShared_2414_ = v_isSharedCheck_2418_;
                        state = 43;
                        continue;
                    }
                }
            }
            19 => {
                if crate::leanh::lean_obj_tag(v_a_2283_) == 1 {
                    crate::leanh::lean_del_object(v___x_2285_);
                    v_val_2287_ = crate::leanh::lean_ctor_get(v_a_2283_, 0);
                    v_isSharedCheck_2405_ = (!crate::leanh::lean_is_exclusive(v_a_2283_)) as u8;
                    if v_isSharedCheck_2405_ == 0 {
                        v___x_2289_ = v_a_2283_;
                        v_isShared_2290_ = v_isSharedCheck_2405_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2287_);
                        crate::leanh::lean_dec(v_a_2283_);
                        v___x_2289_ = crate::leanh::lean_box(0);
                        v_isShared_2290_ = v_isSharedCheck_2405_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2283_);
                    v___x_2406_ = crate::leanh::lean_box(0);
                    if v_isShared_2286_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2285_, 0, v___x_2406_);
                        v___x_2408_ = v___x_2285_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_2409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
                        v___x_2408_ = v_reuseFailAlloc_2409_;
                        state = 42;
                        continue;
                    }
                }
            }
            20 => {
                v_snd_2291_ = crate::leanh::lean_ctor_get(v_val_2287_, 1);
                v_fst_2292_ = crate::leanh::lean_ctor_get(v_val_2287_, 0);
                v_isSharedCheck_2404_ = (!crate::leanh::lean_is_exclusive(v_val_2287_)) as u8;
                if v_isSharedCheck_2404_ == 0 {
                    v___x_2294_ = v_val_2287_;
                    v_isShared_2295_ = v_isSharedCheck_2404_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2291_);
                    crate::leanh::lean_inc(v_fst_2292_);
                    crate::leanh::lean_dec(v_val_2287_);
                    v___x_2294_ = crate::leanh::lean_box(0);
                    v_isShared_2295_ = v_isSharedCheck_2404_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v_fst_2296_ = crate::leanh::lean_ctor_get(v_snd_2291_, 0);
                v_snd_2297_ = crate::leanh::lean_ctor_get(v_snd_2291_, 1);
                v_isSharedCheck_2403_ = (!crate::leanh::lean_is_exclusive(v_snd_2291_)) as u8;
                if v_isSharedCheck_2403_ == 0 {
                    v___x_2299_ = v_snd_2291_;
                    v_isShared_2300_ = v_isSharedCheck_2403_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2297_);
                    crate::leanh::lean_inc(v_fst_2296_);
                    crate::leanh::lean_dec(v_snd_2291_);
                    v___x_2299_ = crate::leanh::lean_box(0);
                    v_isShared_2300_ = v_isSharedCheck_2403_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                crate::leanh::lean_inc(v_snd_2297_);
                v___f_2301_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2301_, 0, v___x_2279_);
                crate::leanh::lean_closure_set(v___f_2301_, 1, v_snd_2297_);
                crate::leanh::lean_inc(v_fst_2292_);
                crate::leanh::lean_inc_ref(v___f_2301_);
                v___x_2302_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_2301_, v_fst_2292_);
                if crate::leanh::lean_obj_tag(v___x_2302_) == 0 {
                    v_a_2303_ = crate::leanh::lean_ctor_get(v___x_2302_, 0);
                    crate::leanh::lean_inc(v_a_2303_);
                    crate::leanh::lean_dec_ref_known(v___x_2302_, 1);
                    crate::leanh::lean_inc(v_fst_2296_);
                    crate::leanh::lean_inc_ref(v___f_2301_);
                    v___x_2304_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_2301_, v_fst_2296_);
                    if crate::leanh::lean_obj_tag(v___x_2304_) == 0 {
                        v_a_2305_ = crate::leanh::lean_ctor_get(v___x_2304_, 0);
                        v_isSharedCheck_2386_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2304_)) as u8;
                        if v_isSharedCheck_2386_ == 0 {
                            v___x_2307_ = v___x_2304_;
                            v_isShared_2308_ = v_isSharedCheck_2386_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2305_);
                            crate::leanh::lean_dec(v___x_2304_);
                            v___x_2307_ = crate::leanh::lean_box(0);
                            v_isShared_2308_ = v_isSharedCheck_2386_;
                            state = 23;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2303_);
                        crate::leanh::lean_dec_ref(v___f_2301_);
                        crate::leanh::lean_del_object(v___x_2299_);
                        crate::leanh::lean_dec(v_snd_2297_);
                        crate::leanh::lean_dec(v_fst_2296_);
                        crate::leanh::lean_del_object(v___x_2294_);
                        crate::leanh::lean_dec(v_fst_2292_);
                        crate::leanh::lean_del_object(v___x_2289_);
                        v_a_2387_ = crate::leanh::lean_ctor_get(v___x_2304_, 0);
                        v_isSharedCheck_2394_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2304_)) as u8;
                        if v_isSharedCheck_2394_ == 0 {
                            v___x_2389_ = v___x_2304_;
                            v_isShared_2390_ = v_isSharedCheck_2394_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2387_);
                            crate::leanh::lean_dec(v___x_2304_);
                            v___x_2389_ = crate::leanh::lean_box(0);
                            v_isShared_2390_ = v_isSharedCheck_2394_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2301_);
                    crate::leanh::lean_del_object(v___x_2299_);
                    crate::leanh::lean_dec(v_snd_2297_);
                    crate::leanh::lean_dec(v_fst_2296_);
                    crate::leanh::lean_del_object(v___x_2294_);
                    crate::leanh::lean_dec(v_fst_2292_);
                    crate::leanh::lean_del_object(v___x_2289_);
                    v_a_2395_ = crate::leanh::lean_ctor_get(v___x_2302_, 0);
                    v_isSharedCheck_2402_ = (!crate::leanh::lean_is_exclusive(v___x_2302_)) as u8;
                    if v_isSharedCheck_2402_ == 0 {
                        v___x_2397_ = v___x_2302_;
                        v_isShared_2398_ = v_isSharedCheck_2402_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2395_);
                        crate::leanh::lean_dec(v___x_2302_);
                        v___x_2397_ = crate::leanh::lean_box(0);
                        v_isShared_2398_ = v_isSharedCheck_2402_;
                        state = 40;
                        continue;
                    }
                }
            }
            23 => {
                v___x_2309_ = l_Lean_mkIntLE(v_a_2303_, v_a_2305_);
                crate::leanh::lean_inc(v_fst_2296_);
                crate::leanh::lean_inc(v_fst_2292_);
                if v_isShared_2295_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2294_, 3);
                    crate::leanh::lean_ctor_set(v___x_2294_, 1, v_fst_2296_);
                    v___x_2311_ = v___x_2294_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2385_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_fst_2292_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_fst_2296_);
                    v___x_2311_ = v_reuseFailAlloc_2385_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_2312_ = l_Int_Linear_Expr_norm(v___x_2311_);
                crate::leanh::lean_dec_ref(v___x_2311_);
                v___x_2313_ = l_Int_Linear_Poly_isUnsatLe(v___x_2312_);
                if v___x_2313_ == 0 {
                    v___x_2314_ = l_Int_Linear_Poly_isValidLe(v___x_2312_);
                    if v___x_2314_ == 0 {
                        crate::leanh::lean_del_object(v___x_2299_);
                        crate::leanh::lean_del_object(v___x_2289_);
                        if v___y_2281_ == 0 {
                            crate::leanh::lean_del_object(v___x_2307_);
                            v___y_2224_ = v_fst_2296_;
                            v___y_2225_ = v___x_2312_;
                            v___y_2226_ = v_fst_2292_;
                            v___y_2227_ = v_snd_2297_;
                            v___y_2228_ = v___f_2301_;
                            v___y_2229_ = v___x_2309_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v___x_2312_);
                            v___x_2315_ = l_Int_Linear_Poly_toExpr(v___x_2312_);
                            v___x_2316_ = l_Int_Linear_instBEqExpr_beq(v___x_2315_, v_fst_2292_);
                            crate::leanh::lean_dec_ref(v___x_2315_);
                            if v___x_2316_ == 0 {
                                crate::leanh::lean_del_object(v___x_2307_);
                                v___y_2224_ = v_fst_2296_;
                                v___y_2225_ = v___x_2312_;
                                v___y_2226_ = v_fst_2292_;
                                v___y_2227_ = v_snd_2297_;
                                v___y_2228_ = v___f_2301_;
                                v___y_2229_ = v___x_2309_;
                                state = 11;
                                continue;
                            } else {
                                v___x_2317_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35,
                                );
                                v___x_2318_ =
                                    l_Int_Linear_instBEqExpr_beq(v_fst_2296_, v___x_2317_);
                                if v___x_2318_ == 0 {
                                    crate::leanh::lean_del_object(v___x_2307_);
                                    v___y_2224_ = v_fst_2296_;
                                    v___y_2225_ = v___x_2312_;
                                    v___y_2226_ = v_fst_2292_;
                                    v___y_2227_ = v_snd_2297_;
                                    v___y_2228_ = v___f_2301_;
                                    v___y_2229_ = v___x_2309_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2312_);
                                    crate::leanh::lean_dec_ref(v___x_2309_);
                                    crate::leanh::lean_dec_ref(v___f_2301_);
                                    crate::leanh::lean_dec(v_snd_2297_);
                                    crate::leanh::lean_dec(v_fst_2296_);
                                    crate::leanh::lean_dec(v_fst_2292_);
                                    v___x_2319_ = crate::leanh::lean_box(0);
                                    if v_isShared_2308_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2307_, 0, v___x_2319_);
                                        v___x_2321_ = v___x_2307_;
                                        state = 25;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2322_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2322_,
                                            0,
                                            v___x_2319_,
                                        );
                                        v___x_2321_ = v_reuseFailAlloc_2322_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2312_);
                        crate::leanh::lean_del_object(v___x_2307_);
                        crate::leanh::lean_dec_ref(v___f_2301_);
                        v___x_2323_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v_snd_2297_,
                            v_a_2107_,
                            v_a_2108_,
                            v_a_2109_,
                            v_a_2110_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2323_) == 0 {
                            v_a_2324_ = crate::leanh::lean_ctor_get(v___x_2323_, 0);
                            v_isSharedCheck_2345_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2323_)) as u8;
                            if v_isSharedCheck_2345_ == 0 {
                                v___x_2326_ = v___x_2323_;
                                v_isShared_2327_ = v_isSharedCheck_2345_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2324_);
                                crate::leanh::lean_dec(v___x_2323_);
                                v___x_2326_ = crate::leanh::lean_box(0);
                                v_isShared_2327_ = v_isSharedCheck_2345_;
                                state = 26;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2309_);
                            crate::leanh::lean_del_object(v___x_2299_);
                            crate::leanh::lean_dec(v_fst_2296_);
                            crate::leanh::lean_dec(v_fst_2292_);
                            crate::leanh::lean_del_object(v___x_2289_);
                            v_a_2346_ = crate::leanh::lean_ctor_get(v___x_2323_, 0);
                            v_isSharedCheck_2353_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2323_)) as u8;
                            if v_isSharedCheck_2353_ == 0 {
                                v___x_2348_ = v___x_2323_;
                                v_isShared_2349_ = v_isSharedCheck_2353_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2346_);
                                crate::leanh::lean_dec(v___x_2323_);
                                v___x_2348_ = crate::leanh::lean_box(0);
                                v_isShared_2349_ = v_isSharedCheck_2353_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2312_);
                    crate::leanh::lean_del_object(v___x_2307_);
                    crate::leanh::lean_dec_ref(v___f_2301_);
                    v___x_2354_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_2297_,
                        v_a_2107_,
                        v_a_2108_,
                        v_a_2109_,
                        v_a_2110_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2354_) == 0 {
                        v_a_2355_ = crate::leanh::lean_ctor_get(v___x_2354_, 0);
                        v_isSharedCheck_2376_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2354_)) as u8;
                        if v_isSharedCheck_2376_ == 0 {
                            v___x_2357_ = v___x_2354_;
                            v_isShared_2358_ = v_isSharedCheck_2376_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2355_);
                            crate::leanh::lean_dec(v___x_2354_);
                            v___x_2357_ = crate::leanh::lean_box(0);
                            v_isShared_2358_ = v_isSharedCheck_2376_;
                            state = 32;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2309_);
                        crate::leanh::lean_del_object(v___x_2299_);
                        crate::leanh::lean_dec(v_fst_2296_);
                        crate::leanh::lean_dec(v_fst_2292_);
                        crate::leanh::lean_del_object(v___x_2289_);
                        v_a_2377_ = crate::leanh::lean_ctor_get(v___x_2354_, 0);
                        v_isSharedCheck_2384_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2354_)) as u8;
                        if v_isSharedCheck_2384_ == 0 {
                            v___x_2379_ = v___x_2354_;
                            v_isShared_2380_ = v_isSharedCheck_2384_;
                            state = 36;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2377_);
                            crate::leanh::lean_dec(v___x_2354_);
                            v___x_2379_ = crate::leanh::lean_box(0);
                            v_isShared_2380_ = v_isSharedCheck_2384_;
                            state = 36;
                            continue;
                        }
                    }
                }
            }
            25 => {
                return v___x_2321_;
            }
            26 => {
                v___x_2328_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38,
                );
                v___x_2329_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11,
                );
                v___x_2330_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_2292_);
                v___x_2331_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_2296_);
                v___x_2332_ = l_Lean_eagerReflBoolTrue;
                v___x_2333_ = l_Lean_mkApp4(
                    v___x_2329_,
                    v_a_2324_,
                    v___x_2330_,
                    v___x_2331_,
                    v___x_2332_,
                );
                v___x_2334_ = l_Lean_mkPropEq(v___x_2309_, v___x_2328_);
                v___x_2335_ = l_Lean_Meta_mkExpectedPropHint(v___x_2333_, v___x_2334_);
                if v_isShared_2300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2299_, 1, v___x_2335_);
                    crate::leanh::lean_ctor_set(v___x_2299_, 0, v___x_2328_);
                    v___x_2337_ = v___x_2299_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2344_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2335_);
                    v___x_2337_ = v_reuseFailAlloc_2344_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2337_);
                    v___x_2339_ = v___x_2289_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2337_);
                    v___x_2339_ = v_reuseFailAlloc_2343_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2326_, 0, v___x_2339_);
                    v___x_2341_ = v___x_2326_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
                    v___x_2341_ = v_reuseFailAlloc_2342_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2341_;
            }
            30 => {
                if v_isShared_2349_ == 0 {
                    v___x_2351_ = v___x_2348_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2352_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
                    v___x_2351_ = v_reuseFailAlloc_2352_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2351_;
            }
            32 => {
                v___x_2359_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8,
                );
                v___x_2360_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14,
                );
                v___x_2361_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_2292_);
                v___x_2362_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_2296_);
                v___x_2363_ = l_Lean_eagerReflBoolTrue;
                v___x_2364_ = l_Lean_mkApp4(
                    v___x_2360_,
                    v_a_2355_,
                    v___x_2361_,
                    v___x_2362_,
                    v___x_2363_,
                );
                v___x_2365_ = l_Lean_mkPropEq(v___x_2309_, v___x_2359_);
                v___x_2366_ = l_Lean_Meta_mkExpectedPropHint(v___x_2364_, v___x_2365_);
                if v_isShared_2300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2299_, 1, v___x_2366_);
                    crate::leanh::lean_ctor_set(v___x_2299_, 0, v___x_2359_);
                    v___x_2368_ = v___x_2299_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2366_);
                    v___x_2368_ = v_reuseFailAlloc_2375_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                if v_isShared_2290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2368_);
                    v___x_2370_ = v___x_2289_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2374_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2368_);
                    v___x_2370_ = v_reuseFailAlloc_2374_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_2358_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2357_, 0, v___x_2370_);
                    v___x_2372_ = v___x_2357_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
                    v___x_2372_ = v_reuseFailAlloc_2373_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2372_;
            }
            36 => {
                if v_isShared_2380_ == 0 {
                    v___x_2382_ = v___x_2379_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
                    v___x_2382_ = v_reuseFailAlloc_2383_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2382_;
            }
            38 => {
                if v_isShared_2390_ == 0 {
                    v___x_2392_ = v___x_2389_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2393_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
                    v___x_2392_ = v_reuseFailAlloc_2393_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2392_;
            }
            40 => {
                if v_isShared_2398_ == 0 {
                    v___x_2400_ = v___x_2397_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2401_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
                    v___x_2400_ = v_reuseFailAlloc_2401_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2400_;
            }
            42 => {
                return v___x_2408_;
            }
            43 => {
                if v_isShared_2414_ == 0 {
                    v___x_2416_ = v___x_2413_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
                    v___x_2416_ = v_reuseFailAlloc_2417_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_2416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(
    mut v_e_2421_: *mut crate::leanh::LeanObject,
    mut v_checkIfModified_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
    mut v_a_2424_: *mut crate::leanh::LeanObject,
    mut v_a_2425_: *mut crate::leanh::LeanObject,
    mut v_a_2426_: *mut crate::leanh::LeanObject,
    mut v_a_2427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkIfModified_boxed_2428_: u8 = 0;
    let mut v_res_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkIfModified_boxed_2428_ = (crate::leanh::lean_unbox(v_checkIfModified_2422_) as u8);
    v_res_2429_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(
        v_e_2421_,
        v_checkIfModified_boxed_2428_,
        v_a_2423_,
        v_a_2424_,
        v_a_2425_,
        v_a_2426_,
    );
    crate::leanh::lean_dec(v_a_2426_);
    crate::leanh::lean_dec_ref(v_a_2425_);
    crate::leanh::lean_dec(v_a_2424_);
    crate::leanh::lean_dec_ref(v_a_2423_);
    return v_res_2429_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = crate::leanh::lean_box(0);
    v___x_2436_ = l_Lean_Level_succ___override(v___x_2435_);
    return v___x_2436_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = crate::leanh::lean_box(0);
    v___x_2438_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3,
    );
    v___x_2439_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2438_);
    crate::leanh::lean_ctor_set(v___x_2439_, 1, v___x_2437_);
    return v___x_2439_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2440_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4,
    );
    v___x_2441_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2;
    v___x_2442_ = l_Lean_mkConst(v___x_2441_, v___x_2440_);
    return v___x_2442_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2443_ = crate::leanh::lean_box(0);
    v___x_2444_ = l_Lean_mkSort(v___x_2443_);
    return v___x_2444_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30,
    );
    v___x_2464_ = l_Lean_mkIntLit(v___x_2463_);
    return v___x_2464_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2469_ = crate::leanh::lean_box(0);
    v___x_2470_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
    v___x_2471_ = l_Lean_mkConst(v___x_2470_, v___x_2469_);
    return v___x_2471_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = crate::leanh::lean_box(0);
    v___x_2477_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23;
    v___x_2478_ = l_Lean_mkConst(v___x_2477_, v___x_2476_);
    return v___x_2478_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2483_ = crate::leanh::lean_box(0);
    v___x_2484_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
    v___x_2485_ = l_Lean_mkConst(v___x_2484_, v___x_2483_);
    return v___x_2485_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = crate::leanh::lean_box(0);
    v___x_2491_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29;
    v___x_2492_ = l_Lean_mkConst(v___x_2491_, v___x_2490_);
    return v___x_2492_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(
    mut v_e_2493_: *mut crate::leanh::LeanObject,
    mut v_a_2494_: *mut crate::leanh::LeanObject,
    mut v_a_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_u2081_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v_val_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v_fst_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2523_: u8 = 0;
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2536_: u8 = 0;
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2543_: u8 = 0;
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: u8 = 0;
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: u8 = 0;
    let mut v_arg_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: u8 = 0;
    let mut v_arg_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    let mut v_arg_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: u8 = 0;
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u8 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: u8 = 0;
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2603_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2623_: u8 = 0;
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2639_: u8 = 0;
    let mut v_a_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2544_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8;
                v___x_2545_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2546_ = l_Lean_Expr_isAppOfArity(v_e_2493_, v___x_2544_, v___x_2545_);
                if v___x_2546_ == 0 {
                    v___x_2547_ = 1;
                    v___x_2548_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(
                        v_e_2493_,
                        v___x_2547_,
                        v_a_2494_,
                        v_a_2495_,
                        v_a_2496_,
                        v_a_2497_,
                    );
                    return v___x_2548_;
                } else {
                    v___x_2549_ = l_Lean_Expr_appArg_x21(v_e_2493_);
                    v___x_2550_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_2549_, v_a_2495_);
                    if crate::leanh::lean_obj_tag(v___x_2550_) == 0 {
                        v_a_2551_ = crate::leanh::lean_ctor_get(v___x_2550_, 0);
                        crate::leanh::lean_inc(v_a_2551_);
                        crate::leanh::lean_dec_ref_known(v___x_2550_, 1);
                        v___x_2552_ = l_Lean_Expr_cleanupAnnotations(v_a_2551_);
                        v___x_2553_ = l_Lean_Expr_isApp(v___x_2552_);
                        if v___x_2553_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2552_);
                            crate::leanh::lean_dec_ref(v_e_2493_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_2554_ = crate::leanh::lean_ctor_get(v___x_2552_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2554_);
                            v___x_2555_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2552_);
                            v___x_2556_ = l_Lean_Expr_isApp(v___x_2555_);
                            if v___x_2556_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2555_);
                                crate::leanh::lean_dec_ref(v_arg_2554_);
                                crate::leanh::lean_dec_ref(v_e_2493_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_2557_ = crate::leanh::lean_ctor_get(v___x_2555_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2557_);
                                v___x_2558_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2555_);
                                v___x_2559_ = l_Lean_Expr_isApp(v___x_2558_);
                                if v___x_2559_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2558_);
                                    crate::leanh::lean_dec_ref(v_arg_2557_);
                                    crate::leanh::lean_dec_ref(v_arg_2554_);
                                    crate::leanh::lean_dec_ref(v_e_2493_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2560_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2558_);
                                    v___x_2561_ = l_Lean_Expr_isApp(v___x_2560_);
                                    if v___x_2561_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2560_);
                                        crate::leanh::lean_dec_ref(v_arg_2557_);
                                        crate::leanh::lean_dec_ref(v_arg_2554_);
                                        crate::leanh::lean_dec_ref(v_e_2493_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_2562_ = crate::leanh::lean_ctor_get(v___x_2560_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_2562_);
                                        v___x_2563_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2560_);
                                        v___x_2564_ =
                                            l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11;
                                        v___x_2565_ =
                                            l_Lean_Expr_isConstOf(v___x_2563_, v___x_2564_);
                                        if v___x_2565_ == 0 {
                                            v___x_2566_ =
                                                l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
                                            v___x_2567_ =
                                                l_Lean_Expr_isConstOf(v___x_2563_, v___x_2566_);
                                            if v___x_2567_ == 0 {
                                                v___x_2568_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
                                                v___x_2569_ =
                                                    l_Lean_Expr_isConstOf(v___x_2563_, v___x_2568_);
                                                if v___x_2569_ == 0 {
                                                    v___x_2570_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17;
                                                    v___x_2571_ = l_Lean_Expr_isConstOf(
                                                        v___x_2563_,
                                                        v___x_2570_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v___x_2563_);
                                                    if v___x_2571_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_2562_);
                                                        crate::leanh::lean_dec_ref(v_arg_2557_);
                                                        crate::leanh::lean_dec_ref(v_arg_2554_);
                                                        crate::leanh::lean_dec_ref(v_e_2493_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_2572_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2562_, v_a_2495_);
                                                        if crate::leanh::lean_obj_tag(v___x_2572_)
                                                            == 0
                                                        {
                                                            v_a_2573_ = crate::leanh::lean_ctor_get(
                                                                v___x_2572_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_2573_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_2572_,
                                                                1,
                                                            );
                                                            v___x_2574_ =
                                                                l_Lean_Expr_cleanupAnnotations(
                                                                    v_a_2573_,
                                                                );
                                                            v___x_2575_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
                                                            v___x_2576_ = l_Lean_Expr_isConstOf(
                                                                v___x_2574_,
                                                                v___x_2575_,
                                                            );
                                                            crate::leanh::lean_dec_ref(v___x_2574_);
                                                            if v___x_2576_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2557_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2554_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_2493_,
                                                                );
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_2577_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
                                                                crate::leanh::lean_inc_ref(
                                                                    v_arg_2554_,
                                                                );
                                                                v___x_2578_ = l_Lean_mkIntAdd(
                                                                    v_arg_2554_,
                                                                    v___x_2577_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_arg_2557_,
                                                                );
                                                                v___x_2579_ = l_Lean_mkIntLE(
                                                                    v___x_2578_,
                                                                    v_arg_2557_,
                                                                );
                                                                v___x_2580_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21);
                                                                v___x_2581_ = l_Lean_mkAppB(
                                                                    v___x_2580_,
                                                                    v_arg_2557_,
                                                                    v_arg_2554_,
                                                                );
                                                                v_val_2503_ = v___x_2579_;
                                                                v_h_u2081_2504_ = v___x_2581_;
                                                                v___y_2505_ = v_a_2494_;
                                                                v___y_2506_ = v_a_2495_;
                                                                v___y_2507_ = v_a_2496_;
                                                                v___y_2508_ = v_a_2497_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_2557_);
                                                            crate::leanh::lean_dec_ref(v_arg_2554_);
                                                            crate::leanh::lean_dec_ref(v_e_2493_);
                                                            v_a_2582_ = crate::leanh::lean_ctor_get(
                                                                v___x_2572_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2589_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2572_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2589_ == 0 {
                                                                v___x_2584_ = v___x_2572_;
                                                                v_isShared_2585_ =
                                                                    v_isSharedCheck_2589_;
                                                                state = 10;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2582_);
                                                                crate::leanh::lean_dec(v___x_2572_);
                                                                v___x_2584_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2585_ =
                                                                    v_isSharedCheck_2589_;
                                                                state = 10;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_2563_);
                                                    v___x_2590_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2562_, v_a_2495_);
                                                    if crate::leanh::lean_obj_tag(v___x_2590_) == 0
                                                    {
                                                        v_a_2591_ = crate::leanh::lean_ctor_get(
                                                            v___x_2590_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_2591_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_2590_,
                                                            1,
                                                        );
                                                        v___x_2592_ =
                                                            l_Lean_Expr_cleanupAnnotations(
                                                                v_a_2591_,
                                                            );
                                                        v___x_2593_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
                                                        v___x_2594_ = l_Lean_Expr_isConstOf(
                                                            v___x_2592_,
                                                            v___x_2593_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v___x_2592_);
                                                        if v___x_2594_ == 0 {
                                                            crate::leanh::lean_dec_ref(v_arg_2557_);
                                                            crate::leanh::lean_dec_ref(v_arg_2554_);
                                                            crate::leanh::lean_dec_ref(v_e_2493_);
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_2595_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
                                                            crate::leanh::lean_inc_ref(v_arg_2557_);
                                                            v___x_2596_ = l_Lean_mkIntAdd(
                                                                v_arg_2557_,
                                                                v___x_2595_,
                                                            );
                                                            crate::leanh::lean_inc_ref(v_arg_2554_);
                                                            v___x_2597_ = l_Lean_mkIntLE(
                                                                v___x_2596_,
                                                                v_arg_2554_,
                                                            );
                                                            v___x_2598_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24);
                                                            v___x_2599_ = l_Lean_mkAppB(
                                                                v___x_2598_,
                                                                v_arg_2557_,
                                                                v_arg_2554_,
                                                            );
                                                            v_val_2503_ = v___x_2597_;
                                                            v_h_u2081_2504_ = v___x_2599_;
                                                            v___y_2505_ = v_a_2494_;
                                                            v___y_2506_ = v_a_2495_;
                                                            v___y_2507_ = v_a_2496_;
                                                            v___y_2508_ = v_a_2497_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_arg_2557_);
                                                        crate::leanh::lean_dec_ref(v_arg_2554_);
                                                        crate::leanh::lean_dec_ref(v_e_2493_);
                                                        v_a_2600_ = crate::leanh::lean_ctor_get(
                                                            v___x_2590_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_2607_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_2590_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2607_ == 0 {
                                                            v___x_2602_ = v___x_2590_;
                                                            v_isShared_2603_ =
                                                                v_isSharedCheck_2607_;
                                                            state = 12;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_2600_);
                                                            crate::leanh::lean_dec(v___x_2590_);
                                                            v___x_2602_ = crate::leanh::lean_box(0);
                                                            v_isShared_2603_ =
                                                                v_isSharedCheck_2607_;
                                                            state = 12;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_2563_);
                                                v___x_2608_ =
                                                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                        v_arg_2562_,
                                                        v_a_2495_,
                                                    );
                                                if crate::leanh::lean_obj_tag(v___x_2608_) == 0 {
                                                    v_a_2609_ =
                                                        crate::leanh::lean_ctor_get(v___x_2608_, 0);
                                                    crate::leanh::lean_inc(v_a_2609_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2608_,
                                                        1,
                                                    );
                                                    v___x_2610_ =
                                                        l_Lean_Expr_cleanupAnnotations(v_a_2609_);
                                                    v___x_2611_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
                                                    v___x_2612_ = l_Lean_Expr_isConstOf(
                                                        v___x_2610_,
                                                        v___x_2611_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v___x_2610_);
                                                    if v___x_2612_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_2557_);
                                                        crate::leanh::lean_dec_ref(v_arg_2554_);
                                                        crate::leanh::lean_dec_ref(v_e_2493_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc_ref(v_arg_2557_);
                                                        crate::leanh::lean_inc_ref(v_arg_2554_);
                                                        v___x_2613_ = l_Lean_mkIntLE(
                                                            v_arg_2554_,
                                                            v_arg_2557_,
                                                        );
                                                        v___x_2614_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27);
                                                        v___x_2615_ = l_Lean_mkAppB(
                                                            v___x_2614_,
                                                            v_arg_2557_,
                                                            v_arg_2554_,
                                                        );
                                                        v_val_2503_ = v___x_2613_;
                                                        v_h_u2081_2504_ = v___x_2615_;
                                                        v___y_2505_ = v_a_2494_;
                                                        v___y_2506_ = v_a_2495_;
                                                        v___y_2507_ = v_a_2496_;
                                                        v___y_2508_ = v_a_2497_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_arg_2557_);
                                                    crate::leanh::lean_dec_ref(v_arg_2554_);
                                                    crate::leanh::lean_dec_ref(v_e_2493_);
                                                    v_a_2616_ =
                                                        crate::leanh::lean_ctor_get(v___x_2608_, 0);
                                                    v_isSharedCheck_2623_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2608_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2623_ == 0 {
                                                        v___x_2618_ = v___x_2608_;
                                                        v_isShared_2619_ = v_isSharedCheck_2623_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2616_);
                                                        crate::leanh::lean_dec(v___x_2608_);
                                                        v___x_2618_ = crate::leanh::lean_box(0);
                                                        v_isShared_2619_ = v_isSharedCheck_2623_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_2563_);
                                            v___x_2624_ =
                                                l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                    v_arg_2562_,
                                                    v_a_2495_,
                                                );
                                            if crate::leanh::lean_obj_tag(v___x_2624_) == 0 {
                                                v_a_2625_ =
                                                    crate::leanh::lean_ctor_get(v___x_2624_, 0);
                                                crate::leanh::lean_inc(v_a_2625_);
                                                crate::leanh::lean_dec_ref_known(v___x_2624_, 1);
                                                v___x_2626_ =
                                                    l_Lean_Expr_cleanupAnnotations(v_a_2625_);
                                                v___x_2627_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
                                                v___x_2628_ =
                                                    l_Lean_Expr_isConstOf(v___x_2626_, v___x_2627_);
                                                crate::leanh::lean_dec_ref(v___x_2626_);
                                                if v___x_2628_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_arg_2557_);
                                                    crate::leanh::lean_dec_ref(v_arg_2554_);
                                                    crate::leanh::lean_dec_ref(v_e_2493_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc_ref(v_arg_2554_);
                                                    crate::leanh::lean_inc_ref(v_arg_2557_);
                                                    v___x_2629_ =
                                                        l_Lean_mkIntLE(v_arg_2557_, v_arg_2554_);
                                                    v___x_2630_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30);
                                                    v___x_2631_ = l_Lean_mkAppB(
                                                        v___x_2630_,
                                                        v_arg_2557_,
                                                        v_arg_2554_,
                                                    );
                                                    v_val_2503_ = v___x_2629_;
                                                    v_h_u2081_2504_ = v___x_2631_;
                                                    v___y_2505_ = v_a_2494_;
                                                    v___y_2506_ = v_a_2495_;
                                                    v___y_2507_ = v_a_2496_;
                                                    v___y_2508_ = v_a_2497_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_arg_2557_);
                                                crate::leanh::lean_dec_ref(v_arg_2554_);
                                                crate::leanh::lean_dec_ref(v_e_2493_);
                                                v_a_2632_ =
                                                    crate::leanh::lean_ctor_get(v___x_2624_, 0);
                                                v_isSharedCheck_2639_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2624_))
                                                        as u8;
                                                if v_isSharedCheck_2639_ == 0 {
                                                    v___x_2634_ = v___x_2624_;
                                                    v_isShared_2635_ = v_isSharedCheck_2639_;
                                                    state = 16;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2632_);
                                                    crate::leanh::lean_dec(v___x_2624_);
                                                    v___x_2634_ = crate::leanh::lean_box(0);
                                                    v_isShared_2635_ = v_isSharedCheck_2639_;
                                                    state = 16;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2493_);
                        v_a_2640_ = crate::leanh::lean_ctor_get(v___x_2550_, 0);
                        v_isSharedCheck_2647_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2550_)) as u8;
                        if v_isSharedCheck_2647_ == 0 {
                            v___x_2642_ = v___x_2550_;
                            v_isShared_2643_ = v_isSharedCheck_2647_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2640_);
                            crate::leanh::lean_dec(v___x_2550_);
                            v___x_2642_ = crate::leanh::lean_box(0);
                            v_isShared_2643_ = v_isSharedCheck_2647_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2500_ = crate::leanh::lean_box(0);
                v___x_2501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2501_, 0, v___x_2500_);
                return v___x_2501_;
            }
            2 => {
                v___x_2509_ = 0;
                crate::leanh::lean_inc_ref(v_val_2503_);
                v___x_2510_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(
                    v_val_2503_,
                    v___x_2509_,
                    v___y_2505_,
                    v___y_2506_,
                    v___y_2507_,
                    v___y_2508_,
                );
                if crate::leanh::lean_obj_tag(v___x_2510_) == 0 {
                    v_a_2511_ = crate::leanh::lean_ctor_get(v___x_2510_, 0);
                    v_isSharedCheck_2543_ = (!crate::leanh::lean_is_exclusive(v___x_2510_)) as u8;
                    if v_isSharedCheck_2543_ == 0 {
                        v___x_2513_ = v___x_2510_;
                        v_isShared_2514_ = v_isSharedCheck_2543_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2511_);
                        crate::leanh::lean_dec(v___x_2510_);
                        v___x_2513_ = crate::leanh::lean_box(0);
                        v_isShared_2514_ = v_isSharedCheck_2543_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_u2081_2504_);
                    crate::leanh::lean_dec_ref(v_val_2503_);
                    crate::leanh::lean_dec_ref(v_e_2493_);
                    return v___x_2510_;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_2511_) == 1 {
                    v_val_2515_ = crate::leanh::lean_ctor_get(v_a_2511_, 0);
                    v_isSharedCheck_2537_ = (!crate::leanh::lean_is_exclusive(v_a_2511_)) as u8;
                    if v_isSharedCheck_2537_ == 0 {
                        v___x_2517_ = v_a_2511_;
                        v_isShared_2518_ = v_isSharedCheck_2537_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2515_);
                        crate::leanh::lean_dec(v_a_2511_);
                        v___x_2517_ = crate::leanh::lean_box(0);
                        v_isShared_2518_ = v_isSharedCheck_2537_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2511_);
                    crate::leanh::lean_dec_ref(v_e_2493_);
                    v___x_2538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2538_, 0, v_val_2503_);
                    crate::leanh::lean_ctor_set(v___x_2538_, 1, v_h_u2081_2504_);
                    v___x_2539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2539_, 0, v___x_2538_);
                    if v_isShared_2514_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2513_, 0, v___x_2539_);
                        v___x_2541_ = v___x_2513_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
                        v___x_2541_ = v_reuseFailAlloc_2542_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2519_ = crate::leanh::lean_ctor_get(v_val_2515_, 0);
                v_snd_2520_ = crate::leanh::lean_ctor_get(v_val_2515_, 1);
                v_isSharedCheck_2536_ = (!crate::leanh::lean_is_exclusive(v_val_2515_)) as u8;
                if v_isSharedCheck_2536_ == 0 {
                    v___x_2522_ = v_val_2515_;
                    v_isShared_2523_ = v_isSharedCheck_2536_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2520_);
                    crate::leanh::lean_inc(v_fst_2519_);
                    crate::leanh::lean_dec(v_val_2515_);
                    v___x_2522_ = crate::leanh::lean_box(0);
                    v_isShared_2523_ = v_isSharedCheck_2536_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2524_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5,
                );
                v___x_2525_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6,
                );
                crate::leanh::lean_inc(v_fst_2519_);
                v___x_2526_ = l_Lean_mkApp6(
                    v___x_2524_,
                    v___x_2525_,
                    v_e_2493_,
                    v_val_2503_,
                    v_fst_2519_,
                    v_h_u2081_2504_,
                    v_snd_2520_,
                );
                if v_isShared_2523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2522_, 1, v___x_2526_);
                    v___x_2528_ = v___x_2522_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_fst_2519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2535_, 1, v___x_2526_);
                    v___x_2528_ = v_reuseFailAlloc_2535_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2517_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2517_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2528_);
                    v___x_2530_ = v_reuseFailAlloc_2534_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2514_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2513_, 0, v___x_2530_);
                    v___x_2532_ = v___x_2513_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
                    v___x_2532_ = v_reuseFailAlloc_2533_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2532_;
            }
            9 => {
                return v___x_2541_;
            }
            10 => {
                if v_isShared_2585_ == 0 {
                    v___x_2587_ = v___x_2584_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
                    v___x_2587_ = v_reuseFailAlloc_2588_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2587_;
            }
            12 => {
                if v_isShared_2603_ == 0 {
                    v___x_2605_ = v___x_2602_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
                    v___x_2605_ = v_reuseFailAlloc_2606_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2605_;
            }
            14 => {
                if v_isShared_2619_ == 0 {
                    v___x_2621_ = v___x_2618_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2622_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
                    v___x_2621_ = v_reuseFailAlloc_2622_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2621_;
            }
            16 => {
                if v_isShared_2635_ == 0 {
                    v___x_2637_ = v___x_2634_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
                    v___x_2637_ = v_reuseFailAlloc_2638_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2637_;
            }
            18 => {
                if v_isShared_2643_ == 0 {
                    v___x_2645_ = v___x_2642_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
                    v___x_2645_ = v_reuseFailAlloc_2646_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2645_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(
    mut v_e_2648_: *mut crate::leanh::LeanObject,
    mut v_a_2649_: *mut crate::leanh::LeanObject,
    mut v_a_2650_: *mut crate::leanh::LeanObject,
    mut v_a_2651_: *mut crate::leanh::LeanObject,
    mut v_a_2652_: *mut crate::leanh::LeanObject,
    mut v_a_2653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2654_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(
        v_e_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_,
    );
    crate::leanh::lean_dec(v_a_2652_);
    crate::leanh::lean_dec_ref(v_a_2651_);
    crate::leanh::lean_dec(v_a_2650_);
    crate::leanh::lean_dec_ref(v_a_2649_);
    return v_res_2654_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(
    mut v_snd_2655_: *mut crate::leanh::LeanObject,
    mut v_x_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2657_ = l_Lean_instInhabitedExpr;
    v___x_2658_ = lean_array_get_borrowed(v___x_2657_, v_snd_2655_, v_x_2656_);
    crate::leanh::lean_inc(v___x_2658_);
    return v___x_2658_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed(
    mut v_snd_2659_: *mut crate::leanh::LeanObject,
    mut v_x_2660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2661_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(v_snd_2659_, v_x_2660_);
    crate::leanh::lean_dec(v_x_2660_);
    crate::leanh::lean_dec_ref(v_snd_2659_);
    return v_res_2661_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = crate::leanh::lean_box(0);
    v___x_2668_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1;
    v___x_2669_ = l_Lean_mkConst(v___x_2668_, v___x_2667_);
    return v___x_2669_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2675_ = crate::leanh::lean_box(0);
    v___x_2676_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4;
    v___x_2677_ = l_Lean_mkConst(v___x_2676_, v___x_2675_);
    return v___x_2677_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = crate::leanh::lean_box(0);
    v___x_2684_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7;
    v___x_2685_ = l_Lean_mkConst(v___x_2684_, v___x_2683_);
    return v___x_2685_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(
    mut v_e_2686_: *mut crate::leanh::LeanObject,
    mut v_a_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
    mut v_a_2689_: *mut crate::leanh::LeanObject,
    mut v_a_2690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2717_: u8 = 0;
    let mut v_val_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2721_: u8 = 0;
    let mut v_snd_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: u8 = 0;
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2773_: u8 = 0;
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2777_: u8 = 0;
    let mut v___x_2778_: u8 = 0;
    let mut v___f_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___y_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: u8 = 0;
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2797_: u8 = 0;
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_a_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: u8 = 0;
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2842_: u8 = 0;
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v_a_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2874_: u8 = 0;
    let mut v_isSharedCheck_2875_: u8 = 0;
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut v_a_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2713_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(
                    v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_,
                );
                if crate::leanh::lean_obj_tag(v___x_2713_) == 0 {
                    v_a_2714_ = crate::leanh::lean_ctor_get(v___x_2713_, 0);
                    v_isSharedCheck_2880_ = (!crate::leanh::lean_is_exclusive(v___x_2713_)) as u8;
                    if v_isSharedCheck_2880_ == 0 {
                        v___x_2716_ = v___x_2713_;
                        v_isShared_2717_ = v_isSharedCheck_2880_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2714_);
                        crate::leanh::lean_dec(v___x_2713_);
                        v___x_2716_ = crate::leanh::lean_box(0);
                        v_isShared_2717_ = v_isSharedCheck_2880_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2881_ = crate::leanh::lean_ctor_get(v___x_2713_, 0);
                    v_isSharedCheck_2888_ = (!crate::leanh::lean_is_exclusive(v___x_2713_)) as u8;
                    if v_isSharedCheck_2888_ == 0 {
                        v___x_2883_ = v___x_2713_;
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2881_);
                        crate::leanh::lean_dec(v___x_2713_);
                        v___x_2883_ = crate::leanh::lean_box(0);
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 26;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2694_);
                v___x_2696_ = l_Lean_mkPropEq(v___y_2693_, v___y_2694_);
                v___x_2697_ = l_Lean_Meta_mkExpectedPropHint(v_h_2695_, v___x_2696_);
                v___x_2698_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2698_, 0, v___y_2694_);
                crate::leanh::lean_ctor_set(v___x_2698_, 1, v___x_2697_);
                v___x_2699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2699_, 0, v___x_2698_);
                v___x_2700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2700_, 0, v___x_2699_);
                return v___x_2700_;
            }
            2 => {
                v___x_2711_ = l_Lean_eagerReflBoolTrue;
                crate::leanh::lean_inc_ref(v___y_2703_);
                v___x_2712_ = l_Lean_mkApp7(
                    v___y_2703_,
                    v___y_2705_,
                    v___y_2709_,
                    v___y_2708_,
                    v___y_2704_,
                    v___y_2707_,
                    v___y_2710_,
                    v___x_2711_,
                );
                v___y_2693_ = v___y_2702_;
                v___y_2694_ = v___y_2706_;
                v_h_2695_ = v___x_2712_;
                state = 1;
                continue;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_2714_) == 1 {
                    v_val_2718_ = crate::leanh::lean_ctor_get(v_a_2714_, 0);
                    v_isSharedCheck_2875_ = (!crate::leanh::lean_is_exclusive(v_a_2714_)) as u8;
                    if v_isSharedCheck_2875_ == 0 {
                        v___x_2720_ = v_a_2714_;
                        v_isShared_2721_ = v_isSharedCheck_2875_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2718_);
                        crate::leanh::lean_dec(v_a_2714_);
                        v___x_2720_ = crate::leanh::lean_box(0);
                        v_isShared_2721_ = v_isSharedCheck_2875_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2714_);
                    v___x_2876_ = crate::leanh::lean_box(0);
                    if v_isShared_2717_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2716_, 0, v___x_2876_);
                        v___x_2878_ = v___x_2716_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_2879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
                        v___x_2878_ = v_reuseFailAlloc_2879_;
                        state = 25;
                        continue;
                    }
                }
            }
            4 => {
                v_snd_2722_ = crate::leanh::lean_ctor_get(v_val_2718_, 1);
                crate::leanh::lean_inc(v_snd_2722_);
                v_fst_2723_ = crate::leanh::lean_ctor_get(v_val_2718_, 0);
                crate::leanh::lean_inc(v_fst_2723_);
                crate::leanh::lean_dec(v_val_2718_);
                v_fst_2724_ = crate::leanh::lean_ctor_get(v_snd_2722_, 0);
                v_snd_2725_ = crate::leanh::lean_ctor_get(v_snd_2722_, 1);
                v_isSharedCheck_2874_ = (!crate::leanh::lean_is_exclusive(v_snd_2722_)) as u8;
                if v_isSharedCheck_2874_ == 0 {
                    v___x_2727_ = v_snd_2722_;
                    v_isShared_2728_ = v_isSharedCheck_2874_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2725_);
                    crate::leanh::lean_inc(v_fst_2724_);
                    crate::leanh::lean_dec(v_snd_2722_);
                    v___x_2727_ = crate::leanh::lean_box(0);
                    v_isShared_2728_ = v_isSharedCheck_2874_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2729_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
                );
                v___x_2778_ = lean_int_dec_eq(v_fst_2723_, v___x_2729_);
                if v___x_2778_ == 0 {
                    crate::leanh::lean_del_object(v___x_2716_);
                    crate::leanh::lean_inc(v_snd_2725_);
                    v___f_2779_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2779_, 0, v_snd_2725_);
                    crate::leanh::lean_inc(v_fst_2724_);
                    crate::leanh::lean_inc_ref(v___f_2779_);
                    v___x_2780_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_2779_, v_fst_2724_);
                    if crate::leanh::lean_obj_tag(v___x_2780_) == 0 {
                        v_a_2781_ = crate::leanh::lean_ctor_get(v___x_2780_, 0);
                        v_isSharedCheck_2861_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2780_)) as u8;
                        if v_isSharedCheck_2861_ == 0 {
                            v___x_2783_ = v___x_2780_;
                            v_isShared_2784_ = v_isSharedCheck_2861_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2781_);
                            crate::leanh::lean_dec(v___x_2780_);
                            v___x_2783_ = crate::leanh::lean_box(0);
                            v_isShared_2784_ = v_isSharedCheck_2861_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_2779_);
                        crate::leanh::lean_del_object(v___x_2727_);
                        crate::leanh::lean_dec(v_snd_2725_);
                        crate::leanh::lean_dec(v_fst_2724_);
                        crate::leanh::lean_dec(v_fst_2723_);
                        crate::leanh::lean_del_object(v___x_2720_);
                        v_a_2862_ = crate::leanh::lean_ctor_get(v___x_2780_, 0);
                        v_isSharedCheck_2869_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2780_)) as u8;
                        if v_isSharedCheck_2869_ == 0 {
                            v___x_2864_ = v___x_2780_;
                            v_isShared_2865_ = v_isSharedCheck_2869_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2862_);
                            crate::leanh::lean_dec(v___x_2780_);
                            v___x_2864_ = crate::leanh::lean_box(0);
                            v_isShared_2865_ = v_isSharedCheck_2869_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2727_);
                    crate::leanh::lean_dec(v_snd_2725_);
                    crate::leanh::lean_dec(v_fst_2724_);
                    crate::leanh::lean_dec(v_fst_2723_);
                    crate::leanh::lean_del_object(v___x_2720_);
                    v___x_2870_ = crate::leanh::lean_box(0);
                    if v_isShared_2717_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2716_, 0, v___x_2870_);
                        v___x_2872_ = v___x_2716_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_2873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
                        v___x_2872_ = v_reuseFailAlloc_2873_;
                        state = 24;
                        continue;
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_2736_);
                v___x_2737_ = l_Lean_mkIntDvd(v___y_2736_, v___y_2733_);
                v___x_2738_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30,
                );
                v___x_2739_ = lean_int_dec_eq(v___y_2734_, v___x_2738_);
                if v___x_2739_ == 0 {
                    v___x_2740_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_2725_,
                        v_a_2687_,
                        v_a_2688_,
                        v_a_2689_,
                        v_a_2690_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2740_) == 0 {
                        v_a_2741_ = crate::leanh::lean_ctor_get(v___x_2740_, 0);
                        crate::leanh::lean_inc(v_a_2741_);
                        crate::leanh::lean_dec_ref_known(v___x_2740_, 1);
                        v___x_2742_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2,
                        );
                        v___x_2743_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_2724_);
                        v___x_2744_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_2732_);
                        v___x_2745_ = lean_int_dec_le(v___x_2729_, v___y_2734_);
                        if v___x_2745_ == 0 {
                            v___x_2746_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                            );
                            v___x_2747_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                            );
                            v___x_2748_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                            );
                            v___x_2749_ = lean_int_neg(v___y_2734_);
                            crate::leanh::lean_dec(v___y_2734_);
                            v___x_2750_ = l_Int_toNat(v___x_2749_);
                            crate::leanh::lean_dec(v___x_2749_);
                            v___x_2751_ = l_Lean_instToExprInt_mkNat(v___x_2750_);
                            v___x_2752_ =
                                l_Lean_mkApp3(v___x_2746_, v___x_2747_, v___x_2748_, v___x_2751_);
                            v___y_2702_ = v___y_2731_;
                            v___y_2703_ = v___x_2742_;
                            v___y_2704_ = v___y_2736_;
                            v___y_2705_ = v_a_2741_;
                            v___y_2706_ = v___x_2737_;
                            v___y_2707_ = v___x_2744_;
                            v___y_2708_ = v___x_2743_;
                            v___y_2709_ = v___y_2735_;
                            v___y_2710_ = v___x_2752_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2753_ = l_Int_toNat(v___y_2734_);
                            crate::leanh::lean_dec(v___y_2734_);
                            v___x_2754_ = l_Lean_instToExprInt_mkNat(v___x_2753_);
                            v___y_2702_ = v___y_2731_;
                            v___y_2703_ = v___x_2742_;
                            v___y_2704_ = v___y_2736_;
                            v___y_2705_ = v_a_2741_;
                            v___y_2706_ = v___x_2737_;
                            v___y_2707_ = v___x_2744_;
                            v___y_2708_ = v___x_2743_;
                            v___y_2709_ = v___y_2735_;
                            v___y_2710_ = v___x_2754_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2737_);
                        crate::leanh::lean_dec_ref(v___y_2736_);
                        crate::leanh::lean_dec_ref(v___y_2735_);
                        crate::leanh::lean_dec(v___y_2734_);
                        crate::leanh::lean_dec_ref(v___y_2732_);
                        crate::leanh::lean_dec_ref(v___y_2731_);
                        crate::leanh::lean_dec(v_fst_2724_);
                        v_a_2755_ = crate::leanh::lean_ctor_get(v___x_2740_, 0);
                        v_isSharedCheck_2762_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2740_)) as u8;
                        if v_isSharedCheck_2762_ == 0 {
                            v___x_2757_ = v___x_2740_;
                            v_isShared_2758_ = v_isSharedCheck_2762_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2755_);
                            crate::leanh::lean_dec(v___x_2740_);
                            v___x_2757_ = crate::leanh::lean_box(0);
                            v_isShared_2758_ = v_isSharedCheck_2762_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2736_);
                    crate::leanh::lean_dec(v___y_2734_);
                    v___x_2763_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_2725_,
                        v_a_2687_,
                        v_a_2688_,
                        v_a_2689_,
                        v_a_2690_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2763_) == 0 {
                        v_a_2764_ = crate::leanh::lean_ctor_get(v___x_2763_, 0);
                        crate::leanh::lean_inc(v_a_2764_);
                        crate::leanh::lean_dec_ref_known(v___x_2763_, 1);
                        v___x_2765_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5,
                        );
                        v___x_2766_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_2724_);
                        v___x_2767_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_2732_);
                        v___x_2768_ = l_Lean_eagerReflBoolTrue;
                        v___x_2769_ = l_Lean_mkApp5(
                            v___x_2765_,
                            v_a_2764_,
                            v___y_2735_,
                            v___x_2766_,
                            v___x_2767_,
                            v___x_2768_,
                        );
                        v___y_2693_ = v___y_2731_;
                        v___y_2694_ = v___x_2737_;
                        v_h_2695_ = v___x_2769_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2737_);
                        crate::leanh::lean_dec_ref(v___y_2735_);
                        crate::leanh::lean_dec_ref(v___y_2732_);
                        crate::leanh::lean_dec_ref(v___y_2731_);
                        crate::leanh::lean_dec(v_fst_2724_);
                        v_a_2770_ = crate::leanh::lean_ctor_get(v___x_2763_, 0);
                        v_isSharedCheck_2777_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2763_)) as u8;
                        if v_isSharedCheck_2777_ == 0 {
                            v___x_2772_ = v___x_2763_;
                            v_isShared_2773_ = v_isSharedCheck_2777_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2770_);
                            crate::leanh::lean_dec(v___x_2763_);
                            v___x_2772_ = crate::leanh::lean_box(0);
                            v_isShared_2773_ = v_isSharedCheck_2777_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if v_isShared_2758_ == 0 {
                    v___x_2760_ = v___x_2757_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
                    v___x_2760_ = v_reuseFailAlloc_2761_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2760_;
            }
            9 => {
                if v_isShared_2773_ == 0 {
                    v___x_2775_ = v___x_2772_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2776_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
                    v___x_2775_ = v_reuseFailAlloc_2776_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2775_;
            }
            11 => {
                v___x_2851_ = lean_int_dec_le(v___x_2729_, v_fst_2723_);
                if v___x_2851_ == 0 {
                    v___x_2852_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                    );
                    v___x_2853_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                    );
                    v___x_2854_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                    );
                    v___x_2855_ = lean_int_neg(v_fst_2723_);
                    v___x_2856_ = l_Int_toNat(v___x_2855_);
                    crate::leanh::lean_dec(v___x_2855_);
                    v___x_2857_ = l_Lean_instToExprInt_mkNat(v___x_2856_);
                    v___x_2858_ = l_Lean_mkApp3(v___x_2852_, v___x_2853_, v___x_2854_, v___x_2857_);
                    v___y_2786_ = v___x_2858_;
                    state = 12;
                    continue;
                } else {
                    v___x_2859_ = l_Int_toNat(v_fst_2723_);
                    v___x_2860_ = l_Lean_instToExprInt_mkNat(v___x_2859_);
                    v___y_2786_ = v___x_2860_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc_ref(v___y_2786_);
                v___x_2787_ = l_Lean_mkIntDvd(v___y_2786_, v_a_2781_);
                v___x_2788_ = l_Int_Linear_Expr_norm(v_fst_2724_);
                crate::leanh::lean_inc(v_fst_2723_);
                v___x_2789_ = l_Int_Linear_Poly_gcdCoeffs(v___x_2788_, v_fst_2723_);
                v___x_2790_ = l_Int_Linear_Poly_getConst(v___x_2788_);
                v___x_2791_ = lean_int_emod(v___x_2790_, v___x_2789_);
                crate::leanh::lean_dec(v___x_2790_);
                v___x_2792_ = lean_int_dec_eq(v___x_2791_, v___x_2729_);
                crate::leanh::lean_dec(v___x_2791_);
                if v___x_2792_ == 0 {
                    crate::leanh::lean_dec(v___x_2789_);
                    crate::leanh::lean_dec_ref(v___x_2788_);
                    crate::leanh::lean_del_object(v___x_2783_);
                    crate::leanh::lean_dec_ref(v___f_2779_);
                    crate::leanh::lean_dec(v_fst_2723_);
                    v___x_2793_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_2725_,
                        v_a_2687_,
                        v_a_2688_,
                        v_a_2689_,
                        v_a_2690_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2793_) == 0 {
                        v_a_2794_ = crate::leanh::lean_ctor_get(v___x_2793_, 0);
                        v_isSharedCheck_2814_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2793_)) as u8;
                        if v_isSharedCheck_2814_ == 0 {
                            v___x_2796_ = v___x_2793_;
                            v_isShared_2797_ = v_isSharedCheck_2814_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2794_);
                            crate::leanh::lean_dec(v___x_2793_);
                            v___x_2796_ = crate::leanh::lean_box(0);
                            v_isShared_2797_ = v_isSharedCheck_2814_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2787_);
                        crate::leanh::lean_dec_ref(v___y_2786_);
                        crate::leanh::lean_del_object(v___x_2727_);
                        crate::leanh::lean_dec(v_fst_2724_);
                        crate::leanh::lean_del_object(v___x_2720_);
                        v_a_2815_ = crate::leanh::lean_ctor_get(v___x_2793_, 0);
                        v_isSharedCheck_2822_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2793_)) as u8;
                        if v_isSharedCheck_2822_ == 0 {
                            v___x_2817_ = v___x_2793_;
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2815_);
                            crate::leanh::lean_dec(v___x_2793_);
                            v___x_2817_ = crate::leanh::lean_box(0);
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2727_);
                    crate::leanh::lean_del_object(v___x_2720_);
                    v___x_2823_ = l_Int_Linear_Poly_div(v___x_2789_, v___x_2788_);
                    crate::leanh::lean_inc_ref(v___x_2823_);
                    v___x_2824_ = l_Int_Linear_Poly_toExpr(v___x_2823_);
                    v___x_2825_ = l_Int_Linear_instBEqExpr_beq(v_fst_2724_, v___x_2824_);
                    crate::leanh::lean_dec_ref(v___x_2824_);
                    if v___x_2825_ == 0 {
                        crate::leanh::lean_del_object(v___x_2783_);
                        crate::leanh::lean_inc_ref(v___x_2823_);
                        v___x_2826_ =
                            l_Int_Linear_Poly_denoteExpr___redArg(v___f_2779_, v___x_2823_);
                        if crate::leanh::lean_obj_tag(v___x_2826_) == 0 {
                            v_a_2827_ = crate::leanh::lean_ctor_get(v___x_2826_, 0);
                            crate::leanh::lean_inc(v_a_2827_);
                            crate::leanh::lean_dec_ref_known(v___x_2826_, 1);
                            v___x_2828_ = lean_int_ediv(v_fst_2723_, v___x_2789_);
                            crate::leanh::lean_dec(v_fst_2723_);
                            v___x_2829_ = lean_int_dec_le(v___x_2729_, v___x_2828_);
                            if v___x_2829_ == 0 {
                                v___x_2830_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                                );
                                v___x_2831_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                );
                                v___x_2832_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                );
                                v___x_2833_ = lean_int_neg(v___x_2828_);
                                crate::leanh::lean_dec(v___x_2828_);
                                v___x_2834_ = l_Int_toNat(v___x_2833_);
                                crate::leanh::lean_dec(v___x_2833_);
                                v___x_2835_ = l_Lean_instToExprInt_mkNat(v___x_2834_);
                                v___x_2836_ = l_Lean_mkApp3(
                                    v___x_2830_,
                                    v___x_2831_,
                                    v___x_2832_,
                                    v___x_2835_,
                                );
                                v___y_2731_ = v___x_2787_;
                                v___y_2732_ = v___x_2823_;
                                v___y_2733_ = v_a_2827_;
                                v___y_2734_ = v___x_2789_;
                                v___y_2735_ = v___y_2786_;
                                v___y_2736_ = v___x_2836_;
                                state = 6;
                                continue;
                            } else {
                                v___x_2837_ = l_Int_toNat(v___x_2828_);
                                crate::leanh::lean_dec(v___x_2828_);
                                v___x_2838_ = l_Lean_instToExprInt_mkNat(v___x_2837_);
                                v___y_2731_ = v___x_2787_;
                                v___y_2732_ = v___x_2823_;
                                v___y_2733_ = v_a_2827_;
                                v___y_2734_ = v___x_2789_;
                                v___y_2735_ = v___y_2786_;
                                v___y_2736_ = v___x_2838_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2823_);
                            crate::leanh::lean_dec(v___x_2789_);
                            crate::leanh::lean_dec_ref(v___x_2787_);
                            crate::leanh::lean_dec_ref(v___y_2786_);
                            crate::leanh::lean_dec(v_snd_2725_);
                            crate::leanh::lean_dec(v_fst_2724_);
                            crate::leanh::lean_dec(v_fst_2723_);
                            v_a_2839_ = crate::leanh::lean_ctor_get(v___x_2826_, 0);
                            v_isSharedCheck_2846_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2826_)) as u8;
                            if v_isSharedCheck_2846_ == 0 {
                                v___x_2841_ = v___x_2826_;
                                v_isShared_2842_ = v_isSharedCheck_2846_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2839_);
                                crate::leanh::lean_dec(v___x_2826_);
                                v___x_2841_ = crate::leanh::lean_box(0);
                                v_isShared_2842_ = v_isSharedCheck_2846_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2823_);
                        crate::leanh::lean_dec(v___x_2789_);
                        crate::leanh::lean_dec_ref(v___x_2787_);
                        crate::leanh::lean_dec_ref(v___y_2786_);
                        crate::leanh::lean_dec_ref(v___f_2779_);
                        crate::leanh::lean_dec(v_snd_2725_);
                        crate::leanh::lean_dec(v_fst_2724_);
                        crate::leanh::lean_dec(v_fst_2723_);
                        v___x_2847_ = crate::leanh::lean_box(0);
                        if v_isShared_2784_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2783_, 0, v___x_2847_);
                            v___x_2849_ = v___x_2783_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_2850_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
                            v___x_2849_ = v_reuseFailAlloc_2850_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            13 => {
                v___x_2798_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8,
                );
                v___x_2799_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8,
                );
                v___x_2800_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_2724_);
                v___x_2801_ = l_Lean_eagerReflBoolTrue;
                v___x_2802_ = l_Lean_mkApp4(
                    v___x_2799_,
                    v_a_2794_,
                    v___y_2786_,
                    v___x_2800_,
                    v___x_2801_,
                );
                v___x_2803_ = l_Lean_mkPropEq(v___x_2787_, v___x_2798_);
                v___x_2804_ = l_Lean_Meta_mkExpectedPropHint(v___x_2802_, v___x_2803_);
                if v_isShared_2728_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2727_, 1, v___x_2804_);
                    crate::leanh::lean_ctor_set(v___x_2727_, 0, v___x_2798_);
                    v___x_2806_ = v___x_2727_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___x_2804_);
                    v___x_2806_ = v_reuseFailAlloc_2813_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2721_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2720_, 0, v___x_2806_);
                    v___x_2808_ = v___x_2720_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2812_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2806_);
                    v___x_2808_ = v_reuseFailAlloc_2812_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2797_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2796_, 0, v___x_2808_);
                    v___x_2810_ = v___x_2796_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2811_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
                    v___x_2810_ = v_reuseFailAlloc_2811_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2810_;
            }
            17 => {
                if v_isShared_2818_ == 0 {
                    v___x_2820_ = v___x_2817_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
                    v___x_2820_ = v_reuseFailAlloc_2821_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2820_;
            }
            19 => {
                if v_isShared_2842_ == 0 {
                    v___x_2844_ = v___x_2841_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
                    v___x_2844_ = v_reuseFailAlloc_2845_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2844_;
            }
            21 => {
                return v___x_2849_;
            }
            22 => {
                if v_isShared_2865_ == 0 {
                    v___x_2867_ = v___x_2864_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
                    v___x_2867_ = v_reuseFailAlloc_2868_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2867_;
            }
            24 => {
                return v___x_2872_;
            }
            25 => {
                return v___x_2878_;
            }
            26 => {
                if v_isShared_2884_ == 0 {
                    v___x_2886_ = v___x_2883_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
                    v___x_2886_ = v_reuseFailAlloc_2887_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(
    mut v_e_2889_: *mut crate::leanh::LeanObject,
    mut v_a_2890_: *mut crate::leanh::LeanObject,
    mut v_a_2891_: *mut crate::leanh::LeanObject,
    mut v_a_2892_: *mut crate::leanh::LeanObject,
    mut v_a_2893_: *mut crate::leanh::LeanObject,
    mut v_a_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(
        v_e_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_,
    );
    crate::leanh::lean_dec(v_a_2893_);
    crate::leanh::lean_dec_ref(v_a_2892_);
    crate::leanh::lean_dec(v_a_2891_);
    crate::leanh::lean_dec_ref(v_a_2890_);
    return v_res_2895_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2903_ = crate::leanh::lean_box(0);
    v___x_2904_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2;
    v___x_2905_ = l_Lean_mkConst(v___x_2904_, v___x_2903_);
    return v___x_2905_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(
    mut v_lhs_2906_: *mut crate::leanh::LeanObject,
    mut v_a_2907_: *mut crate::leanh::LeanObject,
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v_fst_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2921_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2949_: u8 = 0;
    let mut v_a_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2953_: u8 = 0;
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2957_: u8 = 0;
    let mut v_a_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut v_a_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2973_: u8 = 0;
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut v_isSharedCheck_2979_: u8 = 0;
    let mut v_a_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2912_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(
                    v_lhs_2906_,
                    v_a_2907_,
                    v_a_2908_,
                    v_a_2909_,
                    v_a_2910_,
                );
                if crate::leanh::lean_obj_tag(v___x_2912_) == 0 {
                    v_a_2913_ = crate::leanh::lean_ctor_get(v___x_2912_, 0);
                    v_isSharedCheck_2979_ = (!crate::leanh::lean_is_exclusive(v___x_2912_)) as u8;
                    if v_isSharedCheck_2979_ == 0 {
                        v___x_2915_ = v___x_2912_;
                        v_isShared_2916_ = v_isSharedCheck_2979_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2913_);
                        crate::leanh::lean_dec(v___x_2912_);
                        v___x_2915_ = crate::leanh::lean_box(0);
                        v_isShared_2916_ = v_isSharedCheck_2979_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2980_ = crate::leanh::lean_ctor_get(v___x_2912_, 0);
                    v_isSharedCheck_2987_ = (!crate::leanh::lean_is_exclusive(v___x_2912_)) as u8;
                    if v_isSharedCheck_2987_ == 0 {
                        v___x_2982_ = v___x_2912_;
                        v_isShared_2983_ = v_isSharedCheck_2987_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2980_);
                        crate::leanh::lean_dec(v___x_2912_);
                        v___x_2982_ = crate::leanh::lean_box(0);
                        v_isShared_2983_ = v_isSharedCheck_2987_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2917_ = crate::leanh::lean_ctor_get(v_a_2913_, 0);
                v_snd_2918_ = crate::leanh::lean_ctor_get(v_a_2913_, 1);
                v_isSharedCheck_2978_ = (!crate::leanh::lean_is_exclusive(v_a_2913_)) as u8;
                if v_isSharedCheck_2978_ == 0 {
                    v___x_2920_ = v_a_2913_;
                    v_isShared_2921_ = v_isSharedCheck_2978_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2918_);
                    crate::leanh::lean_inc(v_fst_2917_);
                    crate::leanh::lean_dec(v_a_2913_);
                    v___x_2920_ = crate::leanh::lean_box(0);
                    v_isShared_2921_ = v_isSharedCheck_2978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2922_ = l_Int_Linear_Expr_norm(v_fst_2917_);
                crate::leanh::lean_inc_ref(v___x_2922_);
                v___x_2923_ = l_Int_Linear_Poly_toExpr(v___x_2922_);
                v___x_2924_ = l_Int_Linear_instBEqExpr_beq(v_fst_2917_, v___x_2923_);
                crate::leanh::lean_dec_ref(v___x_2923_);
                if v___x_2924_ == 0 {
                    crate::leanh::lean_del_object(v___x_2915_);
                    crate::leanh::lean_inc(v_snd_2918_);
                    v___x_2925_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_2918_,
                        v_a_2907_,
                        v_a_2908_,
                        v_a_2909_,
                        v_a_2910_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2925_) == 0 {
                        v_a_2926_ = crate::leanh::lean_ctor_get(v___x_2925_, 0);
                        crate::leanh::lean_inc(v_a_2926_);
                        crate::leanh::lean_dec_ref_known(v___x_2925_, 1);
                        v___f_2927_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_2927_, 0, v_snd_2918_);
                        crate::leanh::lean_inc(v_fst_2917_);
                        v___x_2928_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_2917_);
                        crate::leanh::lean_inc_ref(v___f_2927_);
                        v___x_2929_ =
                            l_Int_Linear_Expr_denoteExpr___redArg(v___f_2927_, v_fst_2917_);
                        if crate::leanh::lean_obj_tag(v___x_2929_) == 0 {
                            v_a_2930_ = crate::leanh::lean_ctor_get(v___x_2929_, 0);
                            crate::leanh::lean_inc(v_a_2930_);
                            crate::leanh::lean_dec_ref_known(v___x_2929_, 1);
                            crate::leanh::lean_inc_ref(v___x_2922_);
                            v___x_2931_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_2922_);
                            v___x_2932_ =
                                l_Int_Linear_Poly_denoteExpr___redArg(v___f_2927_, v___x_2922_);
                            if crate::leanh::lean_obj_tag(v___x_2932_) == 0 {
                                v_a_2933_ = crate::leanh::lean_ctor_get(v___x_2932_, 0);
                                v_isSharedCheck_2949_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2932_)) as u8;
                                if v_isSharedCheck_2949_ == 0 {
                                    v___x_2935_ = v___x_2932_;
                                    v_isShared_2936_ = v_isSharedCheck_2949_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2933_);
                                    crate::leanh::lean_dec(v___x_2932_);
                                    v___x_2935_ = crate::leanh::lean_box(0);
                                    v_isShared_2936_ = v_isSharedCheck_2949_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2931_);
                                crate::leanh::lean_dec(v_a_2930_);
                                crate::leanh::lean_dec_ref(v___x_2928_);
                                crate::leanh::lean_dec(v_a_2926_);
                                crate::leanh::lean_del_object(v___x_2920_);
                                v_a_2950_ = crate::leanh::lean_ctor_get(v___x_2932_, 0);
                                v_isSharedCheck_2957_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2932_)) as u8;
                                if v_isSharedCheck_2957_ == 0 {
                                    v___x_2952_ = v___x_2932_;
                                    v_isShared_2953_ = v_isSharedCheck_2957_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2950_);
                                    crate::leanh::lean_dec(v___x_2932_);
                                    v___x_2952_ = crate::leanh::lean_box(0);
                                    v_isShared_2953_ = v_isSharedCheck_2957_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2928_);
                            crate::leanh::lean_dec_ref(v___f_2927_);
                            crate::leanh::lean_dec(v_a_2926_);
                            crate::leanh::lean_dec_ref(v___x_2922_);
                            crate::leanh::lean_del_object(v___x_2920_);
                            v_a_2958_ = crate::leanh::lean_ctor_get(v___x_2929_, 0);
                            v_isSharedCheck_2965_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2929_)) as u8;
                            if v_isSharedCheck_2965_ == 0 {
                                v___x_2960_ = v___x_2929_;
                                v_isShared_2961_ = v_isSharedCheck_2965_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2958_);
                                crate::leanh::lean_dec(v___x_2929_);
                                v___x_2960_ = crate::leanh::lean_box(0);
                                v_isShared_2961_ = v_isSharedCheck_2965_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2922_);
                        crate::leanh::lean_del_object(v___x_2920_);
                        crate::leanh::lean_dec(v_snd_2918_);
                        crate::leanh::lean_dec(v_fst_2917_);
                        v_a_2966_ = crate::leanh::lean_ctor_get(v___x_2925_, 0);
                        v_isSharedCheck_2973_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2925_)) as u8;
                        if v_isSharedCheck_2973_ == 0 {
                            v___x_2968_ = v___x_2925_;
                            v_isShared_2969_ = v_isSharedCheck_2973_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2966_);
                            crate::leanh::lean_dec(v___x_2925_);
                            v___x_2968_ = crate::leanh::lean_box(0);
                            v_isShared_2969_ = v_isSharedCheck_2973_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2922_);
                    crate::leanh::lean_del_object(v___x_2920_);
                    crate::leanh::lean_dec(v_snd_2918_);
                    crate::leanh::lean_dec(v_fst_2917_);
                    v___x_2974_ = crate::leanh::lean_box(0);
                    if v_isShared_2916_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2915_, 0, v___x_2974_);
                        v___x_2976_ = v___x_2915_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
                        v___x_2976_ = v_reuseFailAlloc_2977_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2937_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3,
                );
                v___x_2938_ = l_Lean_eagerReflBoolTrue;
                v___x_2939_ = l_Lean_mkApp4(
                    v___x_2937_,
                    v_a_2926_,
                    v___x_2928_,
                    v___x_2931_,
                    v___x_2938_,
                );
                crate::leanh::lean_inc(v_a_2933_);
                v___x_2940_ = l_Lean_mkIntEq(v_a_2930_, v_a_2933_);
                v___x_2941_ = l_Lean_Meta_mkExpectedPropHint(v___x_2939_, v___x_2940_);
                if v_isShared_2921_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2920_, 1, v___x_2941_);
                    crate::leanh::lean_ctor_set(v___x_2920_, 0, v_a_2933_);
                    v___x_2943_ = v___x_2920_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2948_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2941_);
                    v___x_2943_ = v_reuseFailAlloc_2948_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2944_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2944_, 0, v___x_2943_);
                if v_isShared_2936_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2935_, 0, v___x_2944_);
                    v___x_2946_ = v___x_2935_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
                    v___x_2946_ = v_reuseFailAlloc_2947_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2946_;
            }
            6 => {
                if v_isShared_2953_ == 0 {
                    v___x_2955_ = v___x_2952_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
                    v___x_2955_ = v_reuseFailAlloc_2956_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2955_;
            }
            8 => {
                if v_isShared_2961_ == 0 {
                    v___x_2963_ = v___x_2960_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
                    v___x_2963_ = v_reuseFailAlloc_2964_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2963_;
            }
            10 => {
                if v_isShared_2969_ == 0 {
                    v___x_2971_ = v___x_2968_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
                    v___x_2971_ = v_reuseFailAlloc_2972_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2971_;
            }
            12 => {
                return v___x_2976_;
            }
            13 => {
                if v_isShared_2983_ == 0 {
                    v___x_2985_ = v___x_2982_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
                    v___x_2985_ = v_reuseFailAlloc_2986_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(
    mut v_lhs_2988_: *mut crate::leanh::LeanObject,
    mut v_a_2989_: *mut crate::leanh::LeanObject,
    mut v_a_2990_: *mut crate::leanh::LeanObject,
    mut v_a_2991_: *mut crate::leanh::LeanObject,
    mut v_a_2992_: *mut crate::leanh::LeanObject,
    mut v_a_2993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2994_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(
        v_lhs_2988_,
        v_a_2989_,
        v_a_2990_,
        v_a_2991_,
        v_a_2992_,
    );
    crate::leanh::lean_dec(v_a_2992_);
    crate::leanh::lean_dec_ref(v_a_2991_);
    crate::leanh::lean_dec(v_a_2990_);
    crate::leanh::lean_dec_ref(v_a_2989_);
    return v_res_2994_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
}
