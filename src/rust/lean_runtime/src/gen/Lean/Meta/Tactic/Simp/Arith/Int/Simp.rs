// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: Lean.Meta.Tactic.Simp.Arith.Util Lean.Meta.Tactic.Simp.Arith.Int.Basic
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Int::Linear::{
    l_Int_Linear_Expr_norm, l_Int_Linear_Poly_div, l_Int_Linear_Poly_gcdCoeffs,
    l_Int_Linear_Poly_getConst, l_Int_Linear_Poly_isUnsatEq, l_Int_Linear_Poly_isUnsatLe,
    l_Int_Linear_Poly_isValidEq, l_Int_Linear_Poly_isValidLe, l_Int_Linear_instBEqExpr_beq,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_le, lean_int_neg, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Data::Nat::Gcd::lean_nat_gcd;
use crate::lean_imports_rs::Init::Prelude::{lean_array_get_borrowed, lean_nat_dec_eq};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value)
                as *mut LeanObject,
            10060288092756996131 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value)
                as *mut LeanObject,
            907667957179513571 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            101, 113, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 100, 105, 118,
            67, 111, 101, 102, 102, 0,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value)
                as *mut LeanObject,
            15222022325075373211 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value)
                as *mut LeanObject,
            9626815015619986526 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value)
                as *mut LeanObject,
            17185717442815859305 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value)
                as *mut LeanObject,
            6362876895233142233 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value)
                as *mut LeanObject,
            6597761869438004053 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value)
                as *mut LeanObject,
            8912318443281423404 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value)
                as *mut LeanObject,
            8314161943217586311 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value)
                as *mut LeanObject,
            11870096045526947150 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value)
                as *mut LeanObject,
            1301655992456463126 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value)
                as *mut LeanObject,
            397423300456770027 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value)
                as *mut LeanObject,
            10859493989233018008 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            110, 111, 114, 109, 95, 108, 101, 95, 99, 111, 101, 102, 102, 95, 116, 105, 103, 104,
            116, 0,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value)
                as *mut LeanObject,
            14708339156377520116 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value)
                as *mut LeanObject,
            1839820918411524584 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value)
                as *mut LeanObject,
            11529026806789895592 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value)
                as *mut LeanObject,
            9757622324104460876 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value)
                as *mut LeanObject,
            8347582161988589016 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value)
                as *mut LeanObject,
            7316284823769321069 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value)
                as *mut LeanObject,
            17532416664988428445 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value)
                as *mut LeanObject,
            16612019923665488825 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value)
                as *mut LeanObject,
            2272833755566510320 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value)
                as *mut LeanObject,
            9426339939459091439 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value)
                as *mut LeanObject,
            17878876274162330439 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value)
                as *mut LeanObject,
            11833570877100518198 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value)
                as *mut LeanObject,
            1755019837031360842 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value)
                as *mut LeanObject,
            5555145617058846791 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value)
                as *mut LeanObject,
            5162611250653448781 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value)
                as *mut LeanObject,
            330781738820734295 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value)
                as *mut LeanObject,
            3394945094387313110 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value)
                as *mut LeanObject,
            317193488316801530 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value)
                as *mut LeanObject,
            11199380116660155345 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value)
                as *mut LeanObject,
            3792564684362573326 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value)
                as *mut LeanObject,
            13203838950204374860 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value)
                as *mut LeanObject,
            5856160982567210200 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value)
                as *mut LeanObject,
            10556148748237291170 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value)
                as *mut LeanObject,
            2473476115399171125 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(
    mut v_k_1498_: *mut LeanObject,
    mut v_p_1499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: u8 = 0;
    let mut v_k_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1500_ = lean_unsigned_to_nat(1);
                v___x_1501_ = lean_nat_dec_eq(v_k_1498_, v___x_1500_);
                if v___x_1501_ == 0 {
                    if lean_obj_tag(v_p_1499_) == 0 {
                        v_k_1502_ = lean_ctor_get(v_p_1499_, 0);
                        v___x_1503_ = lean_nat_abs(v_k_1502_);
                        v___x_1504_ = lean_nat_gcd(v_k_1498_, v___x_1503_);
                        lean_dec(v___x_1503_);
                        lean_dec(v_k_1498_);
                        return v___x_1504_;
                    } else {
                        v_k_1505_ = lean_ctor_get(v_p_1499_, 0);
                        v_p_1506_ = lean_ctor_get(v_p_1499_, 2);
                        v___x_1507_ = lean_nat_abs(v_k_1505_);
                        v___x_1508_ = lean_nat_gcd(v_k_1498_, v___x_1507_);
                        lean_dec(v___x_1507_);
                        lean_dec(v_k_1498_);
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
    mut v_k_1510_: *mut LeanObject,
    mut v_p_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1512_: *mut LeanObject = core::ptr::null_mut();
    v_res_1512_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(
        v_k_1510_, v_p_1511_,
    );
    lean_dec_ref(v_p_1511_);
    return v_res_1512_;
}
pub unsafe fn l_Int_Linear_Poly_gcdAll(mut v_x_1513_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1513_) == 0 {
        let mut v_k_1514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
        v_k_1514_ = lean_ctor_get(v_x_1513_, 0);
        v___x_1515_ = lean_nat_abs(v_k_1514_);
        return v___x_1515_;
    } else {
        let mut v_k_1516_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
        v_k_1516_ = lean_ctor_get(v_x_1513_, 0);
        v_p_1517_ = lean_ctor_get(v_x_1513_, 2);
        v___x_1518_ = lean_nat_abs(v_k_1516_);
        v___x_1519_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(
            v___x_1518_,
            v_p_1517_,
        );
        return v___x_1519_;
    }
}
pub unsafe fn l_Int_Linear_Poly_gcdAll___boxed(mut v_x_1520_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1521_: *mut LeanObject = core::ptr::null_mut();
    v_res_1521_ = l_Int_Linear_Poly_gcdAll(v_x_1520_);
    lean_dec_ref(v_x_1520_);
    return v_res_1521_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(
    mut v_k_1522_: *mut LeanObject,
    mut v_p_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u8 = 0;
    let mut v_k_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1524_ = lean_unsigned_to_nat(1);
                v___x_1525_ = lean_nat_dec_eq(v_k_1522_, v___x_1524_);
                if v___x_1525_ == 0 {
                    if lean_obj_tag(v_p_1523_) == 0 {
                        return v_k_1522_;
                    } else {
                        v_k_1526_ = lean_ctor_get(v_p_1523_, 0);
                        v_p_1527_ = lean_ctor_get(v_p_1523_, 2);
                        v___x_1528_ = lean_nat_abs(v_k_1526_);
                        v___x_1529_ = lean_nat_gcd(v_k_1522_, v___x_1528_);
                        lean_dec(v___x_1528_);
                        lean_dec(v_k_1522_);
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
    mut v_k_1531_: *mut LeanObject,
    mut v_p_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1533_: *mut LeanObject = core::ptr::null_mut();
    v_res_1533_ =
        l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(
            v_k_1531_, v_p_1532_,
        );
    lean_dec_ref(v_p_1532_);
    return v_res_1533_;
}
pub unsafe fn l_Int_Linear_Poly_gcdCoeffs_x27(mut v_x_1534_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1534_) == 0 {
        let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
        v___x_1535_ = lean_unsigned_to_nat(1);
        return v___x_1535_;
    } else {
        let mut v_k_1536_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
        v_k_1536_ = lean_ctor_get(v_x_1534_, 0);
        v_p_1537_ = lean_ctor_get(v_x_1534_, 2);
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
    mut v_x_1540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1541_: *mut LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_x_1540_);
    lean_dec_ref(v_x_1540_);
    return v_res_1541_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(
    mut v_a_1542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    v___x_1543_ = lean_nat_to_int(v_a_1542_);
    return v___x_1543_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(
    mut v___x_1544_: *mut LeanObject,
    mut v_snd_1545_: *mut LeanObject,
    mut v_x_1546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    v___x_1547_ = lean_array_get_borrowed(v___x_1544_, v_snd_1545_, v_x_1546_);
    lean_inc(v___x_1547_);
    return v___x_1547_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(
    mut v___x_1548_: *mut LeanObject,
    mut v_snd_1549_: *mut LeanObject,
    mut v_x_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1551_: *mut LeanObject = core::ptr::null_mut();
    v_res_1551_ =
        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(v___x_1548_, v_snd_1549_, v_x_1550_);
    lean_dec(v_x_1550_);
    lean_dec_ref(v_snd_1549_);
    lean_dec_ref(v___x_1548_);
    return v_res_1551_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    v___x_1559_ = lean_box(0);
    v___x_1560_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3;
    v___x_1561_ = l_Lean_mkConst(v___x_1560_, v___x_1559_);
    return v___x_1561_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5() -> *mut LeanObject {
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    v___x_1562_ = lean_unsigned_to_nat(0);
    v___x_1563_ = lean_nat_to_int(v___x_1562_);
    return v___x_1563_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8() -> *mut LeanObject {
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    v___x_1567_ = lean_box(0);
    v___x_1568_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7;
    v___x_1569_ = l_Lean_mkConst(v___x_1568_, v___x_1567_);
    return v___x_1569_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11() -> *mut LeanObject {
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    v___x_1575_ = lean_box(0);
    v___x_1576_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10;
    v___x_1577_ = l_Lean_mkConst(v___x_1576_, v___x_1575_);
    return v___x_1577_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15() -> *mut LeanObject {
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    v___x_1583_ = lean_unsigned_to_nat(0);
    v___x_1584_ = l_Lean_Level_ofNat(v___x_1583_);
    return v___x_1584_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16() -> *mut LeanObject {
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    v___x_1585_ = lean_box(0);
    v___x_1586_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15,
    );
    v___x_1587_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1587_, 0, v___x_1586_);
    lean_ctor_set(v___x_1587_, 1, v___x_1585_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17() -> *mut LeanObject {
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    v___x_1588_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16,
    );
    v___x_1589_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
    v___x_1590_ = l_Lean_Expr_const___override(v___x_1589_, v___x_1588_);
    return v___x_1590_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19() -> *mut LeanObject {
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    v___x_1593_ = lean_box(0);
    v___x_1594_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
    v___x_1595_ = l_Lean_Expr_const___override(v___x_1594_, v___x_1593_);
    return v___x_1595_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22() -> *mut LeanObject {
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    v___x_1600_ = lean_box(0);
    v___x_1601_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21;
    v___x_1602_ = l_Lean_Expr_const___override(v___x_1601_, v___x_1600_);
    return v___x_1602_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23() -> *mut LeanObject {
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    v___x_1603_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
    );
    v___x_1604_ = l_Lean_mkIntLit(v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26() -> *mut LeanObject {
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    v___x_1610_ = lean_box(0);
    v___x_1611_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25;
    v___x_1612_ = l_Lean_mkConst(v___x_1611_, v___x_1610_);
    return v___x_1612_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29() -> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618_ = lean_box(0);
    v___x_1619_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28;
    v___x_1620_ = l_Lean_mkConst(v___x_1619_, v___x_1618_);
    return v___x_1620_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30() -> *mut LeanObject {
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    v___x_1621_ = lean_unsigned_to_nat(1);
    v___x_1622_ = lean_nat_to_int(v___x_1621_);
    return v___x_1622_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31() -> *mut LeanObject {
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    v___x_1623_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30,
    );
    v___x_1624_ = lean_int_neg(v___x_1623_);
    return v___x_1624_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34() -> *mut LeanObject {
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    v___x_1630_ = lean_box(0);
    v___x_1631_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33;
    v___x_1632_ = l_Lean_mkConst(v___x_1631_, v___x_1630_);
    return v___x_1632_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35() -> *mut LeanObject {
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    v___x_1633_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
    );
    v___x_1634_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1634_, 0, v___x_1633_);
    return v___x_1634_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38() -> *mut LeanObject {
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    v___x_1638_ = lean_box(0);
    v___x_1639_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37;
    v___x_1640_ = l_Lean_mkConst(v___x_1639_, v___x_1638_);
    return v___x_1640_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41() -> *mut LeanObject {
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    v___x_1646_ = lean_box(0);
    v___x_1647_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40;
    v___x_1648_ = l_Lean_mkConst(v___x_1647_, v___x_1646_);
    return v___x_1648_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44() -> *mut LeanObject {
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    v___x_1654_ = lean_box(0);
    v___x_1655_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43;
    v___x_1656_ = l_Lean_mkConst(v___x_1655_, v___x_1654_);
    return v___x_1656_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(
    mut v_e_1657_: *mut LeanObject,
    mut v_a_1658_: *mut LeanObject,
    mut v_a_1659_: *mut LeanObject,
    mut v_a_1660_: *mut LeanObject,
    mut v_a_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v_val_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v_snd_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v_fst_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1681_: u8 = 0;
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut v_a_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut v_a_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_a_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut v_a_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v___y_1887_: u8 = 0;
    let mut v_k_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v_k_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v_k_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1926_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut v_a_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1956_: u8 = 0;
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_a_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v_a_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v_a_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2023_: u8 = 0;
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2027_: u8 = 0;
    let mut v_isSharedCheck_2028_: u8 = 0;
    let mut v_a_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_isSharedCheck_2037_: u8 = 0;
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut v_a_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1663_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(
                    v_e_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_,
                );
                if lean_obj_tag(v___x_1663_) == 0 {
                    v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
                    v_isSharedCheck_2044_ = (!lean_is_exclusive(v___x_1663_)) as u8;
                    if v_isSharedCheck_2044_ == 0 {
                        v___x_1666_ = v___x_1663_;
                        v_isShared_1667_ = v_isSharedCheck_2044_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1664_);
                        lean_dec(v___x_1663_);
                        v___x_1666_ = lean_box(0);
                        v_isShared_1667_ = v_isSharedCheck_2044_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2045_ = lean_ctor_get(v___x_1663_, 0);
                    v_isSharedCheck_2052_ = (!lean_is_exclusive(v___x_1663_)) as u8;
                    if v_isSharedCheck_2052_ == 0 {
                        v___x_2047_ = v___x_1663_;
                        v_isShared_2048_ = v_isSharedCheck_2052_;
                        state = 54;
                        continue;
                    } else {
                        lean_inc(v_a_2045_);
                        lean_dec(v___x_1663_);
                        v___x_2047_ = lean_box(0);
                        v_isShared_2048_ = v_isSharedCheck_2052_;
                        state = 54;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1664_) == 1 {
                    v_val_1668_ = lean_ctor_get(v_a_1664_, 0);
                    v_isSharedCheck_2039_ = (!lean_is_exclusive(v_a_1664_)) as u8;
                    if v_isSharedCheck_2039_ == 0 {
                        v___x_1670_ = v_a_1664_;
                        v_isShared_1671_ = v_isSharedCheck_2039_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1668_);
                        lean_dec(v_a_1664_);
                        v___x_1670_ = lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_2039_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1664_);
                    v___x_2040_ = lean_box(0);
                    if v_isShared_1667_ == 0 {
                        lean_ctor_set(v___x_1666_, 0, v___x_2040_);
                        v___x_2042_ = v___x_1666_;
                        state = 53;
                        continue;
                    } else {
                        v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
                        v___x_2042_ = v_reuseFailAlloc_2043_;
                        state = 53;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_1672_ = lean_ctor_get(v_val_1668_, 1);
                v_fst_1673_ = lean_ctor_get(v_val_1668_, 0);
                v_isSharedCheck_2038_ = (!lean_is_exclusive(v_val_1668_)) as u8;
                if v_isSharedCheck_2038_ == 0 {
                    v___x_1675_ = v_val_1668_;
                    v_isShared_1676_ = v_isSharedCheck_2038_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_1672_);
                    lean_inc(v_fst_1673_);
                    lean_dec(v_val_1668_);
                    v___x_1675_ = lean_box(0);
                    v_isShared_1676_ = v_isSharedCheck_2038_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_1677_ = lean_ctor_get(v_snd_1672_, 0);
                v_snd_1678_ = lean_ctor_get(v_snd_1672_, 1);
                v_isSharedCheck_2037_ = (!lean_is_exclusive(v_snd_1672_)) as u8;
                if v_isSharedCheck_2037_ == 0 {
                    v___x_1680_ = v_snd_1672_;
                    v_isShared_1681_ = v_isSharedCheck_2037_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_1678_);
                    lean_inc(v_fst_1677_);
                    lean_dec(v_snd_1672_);
                    v___x_1680_ = lean_box(0);
                    v_isShared_1681_ = v_isSharedCheck_2037_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1682_ = l_Lean_instInhabitedExpr;
                lean_inc(v_snd_1678_);
                v___f_1683_ = lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1683_, 0, v___x_1682_);
                lean_closure_set(v___f_1683_, 1, v_snd_1678_);
                lean_inc(v_fst_1673_);
                lean_inc_ref(v___f_1683_);
                v___x_1684_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_1683_, v_fst_1673_);
                if lean_obj_tag(v___x_1684_) == 0 {
                    v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
                    v_isSharedCheck_2028_ = (!lean_is_exclusive(v___x_1684_)) as u8;
                    if v_isSharedCheck_2028_ == 0 {
                        v___x_1687_ = v___x_1684_;
                        v_isShared_1688_ = v_isSharedCheck_2028_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1685_);
                        lean_dec(v___x_1684_);
                        v___x_1687_ = lean_box(0);
                        v_isShared_1688_ = v_isSharedCheck_2028_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_1683_);
                    lean_del_object(v___x_1680_);
                    lean_dec(v_snd_1678_);
                    lean_dec(v_fst_1677_);
                    lean_del_object(v___x_1675_);
                    lean_dec(v_fst_1673_);
                    lean_del_object(v___x_1670_);
                    lean_del_object(v___x_1666_);
                    v_a_2029_ = lean_ctor_get(v___x_1684_, 0);
                    v_isSharedCheck_2036_ = (!lean_is_exclusive(v___x_1684_)) as u8;
                    if v_isSharedCheck_2036_ == 0 {
                        v___x_2031_ = v___x_1684_;
                        v_isShared_2032_ = v_isSharedCheck_2036_;
                        state = 51;
                        continue;
                    } else {
                        lean_inc(v_a_2029_);
                        lean_dec(v___x_1684_);
                        v___x_2031_ = lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2036_;
                        state = 51;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_fst_1677_);
                lean_inc_ref(v___f_1683_);
                v___x_1689_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_1683_, v_fst_1677_);
                if lean_obj_tag(v___x_1689_) == 0 {
                    v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
                    v_isSharedCheck_2019_ = (!lean_is_exclusive(v___x_1689_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_1692_ = v___x_1689_;
                        v_isShared_1693_ = v_isSharedCheck_2019_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1690_);
                        lean_dec(v___x_1689_);
                        v___x_1692_ = lean_box(0);
                        v_isShared_1693_ = v_isSharedCheck_2019_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1687_);
                    lean_dec(v_a_1685_);
                    lean_dec_ref(v___f_1683_);
                    lean_del_object(v___x_1680_);
                    lean_dec(v_snd_1678_);
                    lean_dec(v_fst_1677_);
                    lean_del_object(v___x_1675_);
                    lean_dec(v_fst_1673_);
                    lean_del_object(v___x_1670_);
                    lean_del_object(v___x_1666_);
                    v_a_2020_ = lean_ctor_get(v___x_1689_, 0);
                    v_isSharedCheck_2027_ = (!lean_is_exclusive(v___x_1689_)) as u8;
                    if v_isSharedCheck_2027_ == 0 {
                        v___x_2022_ = v___x_1689_;
                        v_isShared_2023_ = v_isSharedCheck_2027_;
                        state = 49;
                        continue;
                    } else {
                        lean_inc(v_a_2020_);
                        lean_dec(v___x_1689_);
                        v___x_2022_ = lean_box(0);
                        v_isShared_2023_ = v_isSharedCheck_2027_;
                        state = 49;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1694_ = l_Lean_mkIntEq(v_a_1685_, v_a_1690_);
                lean_inc(v_fst_1677_);
                lean_inc(v_fst_1673_);
                v___x_1771_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_1771_, 0, v_fst_1673_);
                lean_ctor_set(v___x_1771_, 1, v_fst_1677_);
                v___x_1772_ = l_Int_Linear_Expr_norm(v___x_1771_);
                lean_dec_ref_known(v___x_1771_, 2);
                v___x_1959_ = l_Int_Linear_Poly_isUnsatEq(v___x_1772_);
                if v___x_1959_ == 0 {
                    v___x_1960_ = l_Int_Linear_Poly_isValidEq(v___x_1772_);
                    if v___x_1960_ == 0 {
                        lean_inc_ref(v___x_1772_);
                        v___x_1961_ = l_Int_Linear_Poly_toExpr(v___x_1772_);
                        v___x_1962_ = l_Int_Linear_instBEqExpr_beq(v___x_1961_, v_fst_1673_);
                        lean_dec_ref(v___x_1961_);
                        if v___x_1962_ == 0 {
                            v___y_1887_ = v___x_1962_;
                            state = 33;
                            continue;
                        } else {
                            v___x_1963_ = lean_obj_once(
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
                        lean_dec_ref(v___x_1772_);
                        lean_del_object(v___x_1692_);
                        lean_del_object(v___x_1687_);
                        lean_dec_ref(v___f_1683_);
                        lean_del_object(v___x_1680_);
                        lean_del_object(v___x_1675_);
                        lean_del_object(v___x_1670_);
                        lean_del_object(v___x_1666_);
                        v___x_1965_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v_snd_1678_,
                            v_a_1658_,
                            v_a_1659_,
                            v_a_1660_,
                            v_a_1661_,
                        );
                        if lean_obj_tag(v___x_1965_) == 0 {
                            v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
                            v_isSharedCheck_1983_ = (!lean_is_exclusive(v___x_1965_)) as u8;
                            if v_isSharedCheck_1983_ == 0 {
                                v___x_1968_ = v___x_1965_;
                                v_isShared_1969_ = v_isSharedCheck_1983_;
                                state = 41;
                                continue;
                            } else {
                                lean_inc(v_a_1966_);
                                lean_dec(v___x_1965_);
                                v___x_1968_ = lean_box(0);
                                v_isShared_1969_ = v_isSharedCheck_1983_;
                                state = 41;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_1694_);
                            lean_dec(v_fst_1677_);
                            lean_dec(v_fst_1673_);
                            v_a_1984_ = lean_ctor_get(v___x_1965_, 0);
                            v_isSharedCheck_1991_ = (!lean_is_exclusive(v___x_1965_)) as u8;
                            if v_isSharedCheck_1991_ == 0 {
                                v___x_1986_ = v___x_1965_;
                                v_isShared_1987_ = v_isSharedCheck_1991_;
                                state = 43;
                                continue;
                            } else {
                                lean_inc(v_a_1984_);
                                lean_dec(v___x_1965_);
                                v___x_1986_ = lean_box(0);
                                v_isShared_1987_ = v_isSharedCheck_1991_;
                                state = 43;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1772_);
                    lean_del_object(v___x_1692_);
                    lean_del_object(v___x_1687_);
                    lean_dec_ref(v___f_1683_);
                    lean_del_object(v___x_1680_);
                    lean_del_object(v___x_1675_);
                    lean_del_object(v___x_1670_);
                    lean_del_object(v___x_1666_);
                    v___x_1992_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_1678_,
                        v_a_1658_,
                        v_a_1659_,
                        v_a_1660_,
                        v_a_1661_,
                    );
                    if lean_obj_tag(v___x_1992_) == 0 {
                        v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
                        v_isSharedCheck_2010_ = (!lean_is_exclusive(v___x_1992_)) as u8;
                        if v_isSharedCheck_2010_ == 0 {
                            v___x_1995_ = v___x_1992_;
                            v_isShared_1996_ = v_isSharedCheck_2010_;
                            state = 45;
                            continue;
                        } else {
                            lean_inc(v_a_1993_);
                            lean_dec(v___x_1992_);
                            v___x_1995_ = lean_box(0);
                            v_isShared_1996_ = v_isSharedCheck_2010_;
                            state = 45;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1694_);
                        lean_dec(v_fst_1677_);
                        lean_dec(v_fst_1673_);
                        v_a_2011_ = lean_ctor_get(v___x_1992_, 0);
                        v_isSharedCheck_2018_ = (!lean_is_exclusive(v___x_1992_)) as u8;
                        if v_isSharedCheck_2018_ == 0 {
                            v___x_2013_ = v___x_1992_;
                            v_isShared_2014_ = v_isSharedCheck_2018_;
                            state = 47;
                            continue;
                        } else {
                            lean_inc(v_a_2011_);
                            lean_dec(v___x_1992_);
                            v___x_2013_ = lean_box(0);
                            v_isShared_2014_ = v_isSharedCheck_2018_;
                            state = 47;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_1702_ = l_Lean_eagerReflBoolTrue;
                lean_inc_ref(v___y_1697_);
                v___x_1703_ = l_Lean_mkApp5(
                    v___y_1697_,
                    v___y_1696_,
                    v___y_1699_,
                    v___y_1700_,
                    v___y_1701_,
                    v___x_1702_,
                );
                lean_inc_ref_n(v___y_1698_, 2);
                v___x_1704_ = l_Lean_mkPropEq(v___x_1694_, v___y_1698_);
                v___x_1705_ = l_Lean_Meta_mkExpectedPropHint(v___x_1703_, v___x_1704_);
                if v_isShared_1681_ == 0 {
                    lean_ctor_set(v___x_1680_, 1, v___x_1705_);
                    lean_ctor_set(v___x_1680_, 0, v___y_1698_);
                    v___x_1707_ = v___x_1680_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___y_1698_);
                    lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1705_);
                    v___x_1707_ = v_reuseFailAlloc_1714_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1671_ == 0 {
                    lean_ctor_set(v___x_1670_, 0, v___x_1707_);
                    v___x_1709_ = v___x_1670_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1707_);
                    v___x_1709_ = v_reuseFailAlloc_1713_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1693_ == 0 {
                    lean_ctor_set(v___x_1692_, 0, v___x_1709_);
                    v___x_1711_ = v___x_1692_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
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
                lean_inc_ref(v___y_1719_);
                v___x_1724_ = l_Lean_mkApp6(
                    v___y_1719_,
                    v___y_1717_,
                    v___y_1718_,
                    v___y_1716_,
                    v___y_1721_,
                    v___y_1722_,
                    v___x_1723_,
                );
                lean_inc_ref(v___y_1720_);
                v___x_1725_ = l_Lean_mkPropEq(v___x_1694_, v___y_1720_);
                v___x_1726_ = l_Lean_Meta_mkExpectedPropHint(v___x_1724_, v___x_1725_);
                if v_isShared_1676_ == 0 {
                    lean_ctor_set(v___x_1675_, 1, v___x_1726_);
                    lean_ctor_set(v___x_1675_, 0, v___y_1720_);
                    v___x_1728_ = v___x_1675_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___y_1720_);
                    lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1726_);
                    v___x_1728_ = v_reuseFailAlloc_1733_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1729_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1729_, 0, v___x_1728_);
                if v_isShared_1688_ == 0 {
                    lean_ctor_set(v___x_1687_, 0, v___x_1729_);
                    v___x_1731_ = v___x_1687_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
                    v___x_1731_ = v_reuseFailAlloc_1732_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1731_;
            }
            14 => {
                lean_inc_ref(v___y_1737_);
                v___x_1738_ = l_Lean_mkIntEq(v___y_1735_, v___y_1737_);
                v___x_1739_ = lean_expr_eqv(v___x_1738_, v___x_1694_);
                if v___x_1739_ == 0 {
                    lean_del_object(v___x_1666_);
                    v___x_1740_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_1678_,
                        v_a_1658_,
                        v_a_1659_,
                        v_a_1660_,
                        v_a_1661_,
                    );
                    if lean_obj_tag(v___x_1740_) == 0 {
                        v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
                        v_isSharedCheck_1758_ = (!lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1758_ == 0 {
                            v___x_1743_ = v___x_1740_;
                            v_isShared_1744_ = v_isSharedCheck_1758_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_1741_);
                            lean_dec(v___x_1740_);
                            v___x_1743_ = lean_box(0);
                            v_isShared_1744_ = v_isSharedCheck_1758_;
                            state = 15;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1738_);
                        lean_dec_ref(v___y_1737_);
                        lean_dec(v___y_1736_);
                        lean_dec_ref(v___x_1694_);
                        lean_dec(v_fst_1677_);
                        lean_dec(v_fst_1673_);
                        v_a_1759_ = lean_ctor_get(v___x_1740_, 0);
                        v_isSharedCheck_1766_ = (!lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1766_ == 0 {
                            v___x_1761_ = v___x_1740_;
                            v_isShared_1762_ = v_isSharedCheck_1766_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_1759_);
                            lean_dec(v___x_1740_);
                            v___x_1761_ = lean_box(0);
                            v_isShared_1762_ = v_isSharedCheck_1766_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1738_);
                    lean_dec_ref(v___y_1737_);
                    lean_dec(v___y_1736_);
                    lean_dec_ref(v___x_1694_);
                    lean_dec(v_snd_1678_);
                    lean_dec(v_fst_1677_);
                    lean_dec(v_fst_1673_);
                    v___x_1767_ = lean_box(0);
                    if v_isShared_1667_ == 0 {
                        lean_ctor_set(v___x_1666_, 0, v___x_1767_);
                        v___x_1769_ = v___x_1666_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
                        v___x_1769_ = v_reuseFailAlloc_1770_;
                        state = 19;
                        continue;
                    }
                }
            }
            15 => {
                v___x_1745_ = lean_obj_once(
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
                lean_inc_ref(v___x_1738_);
                v___x_1751_ = l_Lean_mkPropEq(v___x_1694_, v___x_1738_);
                v___x_1752_ = l_Lean_Meta_mkExpectedPropHint(v___x_1750_, v___x_1751_);
                v___x_1753_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1753_, 0, v___x_1738_);
                lean_ctor_set(v___x_1753_, 1, v___x_1752_);
                v___x_1754_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1754_, 0, v___x_1753_);
                if v_isShared_1744_ == 0 {
                    lean_ctor_set(v___x_1743_, 0, v___x_1754_);
                    v___x_1756_ = v___x_1743_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
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
                    v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
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
                v___x_1779_ = lean_unsigned_to_nat(1);
                v___x_1780_ = lean_nat_dec_eq(v___x_1778_, v___x_1779_);
                if v___x_1780_ == 0 {
                    v___x_1781_ = l_Int_Linear_Poly_getConst(v___x_1772_);
                    v___x_1782_ = lean_nat_to_int(v___x_1778_);
                    v___x_1783_ = lean_int_emod(v___x_1781_, v___x_1782_);
                    lean_dec(v___x_1781_);
                    v___x_1784_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
                    );
                    v___x_1785_ = lean_int_dec_eq(v___x_1783_, v___x_1784_);
                    lean_dec(v___x_1783_);
                    if v___x_1785_ == 0 {
                        lean_dec_ref(v___x_1772_);
                        lean_del_object(v___x_1687_);
                        lean_dec_ref(v___f_1683_);
                        lean_del_object(v___x_1675_);
                        v___x_1786_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v_snd_1678_,
                            v___y_1774_,
                            v___y_1775_,
                            v___y_1776_,
                            v___y_1777_,
                        );
                        if lean_obj_tag(v___x_1786_) == 0 {
                            v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
                            lean_inc(v_a_1787_);
                            lean_dec_ref_known(v___x_1786_, 1);
                            v___x_1788_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8,
                            );
                            v___x_1789_ = lean_obj_once(
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
                                v___x_1793_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                                );
                                v___x_1794_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                );
                                v___x_1795_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                );
                                v___x_1796_ = lean_int_neg(v___x_1782_);
                                lean_dec(v___x_1782_);
                                v___x_1797_ = l_Int_toNat(v___x_1796_);
                                lean_dec(v___x_1796_);
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
                                lean_dec(v___x_1782_);
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
                            lean_dec(v___x_1782_);
                            lean_dec_ref(v___x_1694_);
                            lean_del_object(v___x_1692_);
                            lean_del_object(v___x_1680_);
                            lean_dec(v_fst_1677_);
                            lean_dec(v_fst_1673_);
                            lean_del_object(v___x_1670_);
                            v_a_1802_ = lean_ctor_get(v___x_1786_, 0);
                            v_isSharedCheck_1809_ = (!lean_is_exclusive(v___x_1786_)) as u8;
                            if v_isSharedCheck_1809_ == 0 {
                                v___x_1804_ = v___x_1786_;
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_1802_);
                                lean_dec(v___x_1786_);
                                v___x_1804_ = lean_box(0);
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_1692_);
                        lean_del_object(v___x_1680_);
                        lean_del_object(v___x_1670_);
                        v___x_1810_ = l_Int_Linear_Poly_div(v___x_1782_, v___x_1772_);
                        lean_inc_ref(v___x_1810_);
                        v___x_1811_ =
                            l_Int_Linear_Poly_denoteExpr___redArg(v___f_1683_, v___x_1810_);
                        if lean_obj_tag(v___x_1811_) == 0 {
                            v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
                            lean_inc(v_a_1812_);
                            lean_dec_ref_known(v___x_1811_, 1);
                            v___x_1813_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                                v_snd_1678_,
                                v___y_1774_,
                                v___y_1775_,
                                v___y_1776_,
                                v___y_1777_,
                            );
                            if lean_obj_tag(v___x_1813_) == 0 {
                                v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
                                lean_inc(v_a_1814_);
                                lean_dec_ref_known(v___x_1813_, 1);
                                v___x_1815_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23,
                                );
                                v___x_1816_ = l_Lean_mkIntEq(v_a_1812_, v___x_1815_);
                                v___x_1817_ = lean_obj_once(
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
                                    v___x_1822_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                                    );
                                    v___x_1823_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                    );
                                    v___x_1824_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                    );
                                    v___x_1825_ = lean_int_neg(v___x_1782_);
                                    lean_dec(v___x_1782_);
                                    v___x_1826_ = l_Int_toNat(v___x_1825_);
                                    lean_dec(v___x_1825_);
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
                                    lean_dec(v___x_1782_);
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
                                lean_dec(v_a_1812_);
                                lean_dec_ref(v___x_1810_);
                                lean_dec(v___x_1782_);
                                lean_dec_ref(v___x_1694_);
                                lean_del_object(v___x_1687_);
                                lean_dec(v_fst_1677_);
                                lean_del_object(v___x_1675_);
                                lean_dec(v_fst_1673_);
                                v_a_1831_ = lean_ctor_get(v___x_1813_, 0);
                                v_isSharedCheck_1838_ = (!lean_is_exclusive(v___x_1813_)) as u8;
                                if v_isSharedCheck_1838_ == 0 {
                                    v___x_1833_ = v___x_1813_;
                                    v_isShared_1834_ = v_isSharedCheck_1838_;
                                    state = 23;
                                    continue;
                                } else {
                                    lean_inc(v_a_1831_);
                                    lean_dec(v___x_1813_);
                                    v___x_1833_ = lean_box(0);
                                    v_isShared_1834_ = v_isSharedCheck_1838_;
                                    state = 23;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_1810_);
                            lean_dec(v___x_1782_);
                            lean_dec_ref(v___x_1694_);
                            lean_del_object(v___x_1687_);
                            lean_dec(v_snd_1678_);
                            lean_dec(v_fst_1677_);
                            lean_del_object(v___x_1675_);
                            lean_dec(v_fst_1673_);
                            v_a_1839_ = lean_ctor_get(v___x_1811_, 0);
                            v_isSharedCheck_1846_ = (!lean_is_exclusive(v___x_1811_)) as u8;
                            if v_isSharedCheck_1846_ == 0 {
                                v___x_1841_ = v___x_1811_;
                                v_isShared_1842_ = v_isSharedCheck_1846_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_1839_);
                                lean_dec(v___x_1811_);
                                v___x_1841_ = lean_box(0);
                                v_isShared_1842_ = v_isSharedCheck_1846_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_1778_);
                    lean_del_object(v___x_1692_);
                    lean_del_object(v___x_1687_);
                    lean_del_object(v___x_1680_);
                    lean_del_object(v___x_1675_);
                    lean_del_object(v___x_1670_);
                    lean_inc_ref(v___x_1772_);
                    v___x_1847_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_1683_, v___x_1772_);
                    if lean_obj_tag(v___x_1847_) == 0 {
                        v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
                        lean_inc(v_a_1848_);
                        lean_dec_ref_known(v___x_1847_, 1);
                        v___x_1849_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v_snd_1678_,
                            v___y_1774_,
                            v___y_1775_,
                            v___y_1776_,
                            v___y_1777_,
                        );
                        if lean_obj_tag(v___x_1849_) == 0 {
                            v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
                            v_isSharedCheck_1869_ = (!lean_is_exclusive(v___x_1849_)) as u8;
                            if v_isSharedCheck_1869_ == 0 {
                                v___x_1852_ = v___x_1849_;
                                v_isShared_1853_ = v_isSharedCheck_1869_;
                                state = 27;
                                continue;
                            } else {
                                lean_inc(v_a_1850_);
                                lean_dec(v___x_1849_);
                                v___x_1852_ = lean_box(0);
                                v_isShared_1853_ = v_isSharedCheck_1869_;
                                state = 27;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1848_);
                            lean_dec_ref(v___x_1772_);
                            lean_dec_ref(v___x_1694_);
                            lean_dec(v_fst_1677_);
                            lean_dec(v_fst_1673_);
                            v_a_1870_ = lean_ctor_get(v___x_1849_, 0);
                            v_isSharedCheck_1877_ = (!lean_is_exclusive(v___x_1849_)) as u8;
                            if v_isSharedCheck_1877_ == 0 {
                                v___x_1872_ = v___x_1849_;
                                v_isShared_1873_ = v_isSharedCheck_1877_;
                                state = 29;
                                continue;
                            } else {
                                lean_inc(v_a_1870_);
                                lean_dec(v___x_1849_);
                                v___x_1872_ = lean_box(0);
                                v_isShared_1873_ = v_isSharedCheck_1877_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_1772_);
                        lean_dec_ref(v___x_1694_);
                        lean_dec(v_snd_1678_);
                        lean_dec(v_fst_1677_);
                        lean_dec(v_fst_1673_);
                        v_a_1878_ = lean_ctor_get(v___x_1847_, 0);
                        v_isSharedCheck_1885_ = (!lean_is_exclusive(v___x_1847_)) as u8;
                        if v_isSharedCheck_1885_ == 0 {
                            v___x_1880_ = v___x_1847_;
                            v_isShared_1881_ = v_isSharedCheck_1885_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_1878_);
                            lean_dec(v___x_1847_);
                            v___x_1880_ = lean_box(0);
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
                    v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
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
                    v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
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
                    v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
                    v___x_1844_ = v_reuseFailAlloc_1845_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1844_;
            }
            27 => {
                v___x_1854_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23,
                );
                v___x_1855_ = l_Lean_mkIntEq(v_a_1848_, v___x_1854_);
                v___x_1856_ = lean_obj_once(
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
                lean_inc_ref(v___x_1855_);
                v___x_1862_ = l_Lean_mkPropEq(v___x_1694_, v___x_1855_);
                v___x_1863_ = l_Lean_Meta_mkExpectedPropHint(v___x_1861_, v___x_1862_);
                v___x_1864_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1864_, 0, v___x_1855_);
                lean_ctor_set(v___x_1864_, 1, v___x_1863_);
                v___x_1865_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1865_, 0, v___x_1864_);
                if v_isShared_1853_ == 0 {
                    lean_ctor_set(v___x_1852_, 0, v___x_1865_);
                    v___x_1867_ = v___x_1852_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
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
                    v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
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
                    v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
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
                    if lean_obj_tag(v___x_1772_) == 1 {
                        v_k_1888_ = lean_ctor_get(v___x_1772_, 0);
                        lean_inc(v_k_1888_);
                        v_v_1889_ = lean_ctor_get(v___x_1772_, 1);
                        lean_inc(v_v_1889_);
                        v_p_1890_ = lean_ctor_get(v___x_1772_, 2);
                        lean_inc_ref(v_p_1890_);
                        v___x_1891_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30,
                        );
                        v___x_1892_ = lean_int_dec_eq(v_k_1888_, v___x_1891_);
                        lean_dec(v_k_1888_);
                        if v___x_1892_ == 0 {
                            lean_dec_ref(v_p_1890_);
                            lean_dec(v_v_1889_);
                            lean_del_object(v___x_1666_);
                            v___y_1774_ = v_a_1658_;
                            v___y_1775_ = v_a_1659_;
                            v___y_1776_ = v_a_1660_;
                            v___y_1777_ = v_a_1661_;
                            state = 20;
                            continue;
                        } else {
                            if lean_obj_tag(v_p_1890_) == 0 {
                                lean_dec_ref_known(v___x_1772_, 3);
                                lean_del_object(v___x_1692_);
                                lean_del_object(v___x_1687_);
                                lean_dec_ref(v___f_1683_);
                                lean_del_object(v___x_1680_);
                                lean_del_object(v___x_1675_);
                                lean_del_object(v___x_1670_);
                                v_k_1893_ = lean_ctor_get(v_p_1890_, 0);
                                lean_inc(v_k_1893_);
                                lean_dec_ref_known(v_p_1890_, 1);
                                v___x_1894_ =
                                    lean_array_get_borrowed(v___x_1682_, v_snd_1678_, v_v_1889_);
                                v___x_1895_ = lean_int_neg(v_k_1893_);
                                lean_dec(v_k_1893_);
                                v___x_1896_ = lean_obj_once(
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
                                    v___x_1898_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                                    );
                                    v___x_1899_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                    );
                                    v___x_1900_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                        ),
                                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                    );
                                    v___x_1901_ = lean_int_neg(v___x_1895_);
                                    lean_dec(v___x_1895_);
                                    v___x_1902_ = l_Int_toNat(v___x_1901_);
                                    lean_dec(v___x_1901_);
                                    v___x_1903_ = l_Lean_instToExprInt_mkNat(v___x_1902_);
                                    v___x_1904_ = l_Lean_mkApp3(
                                        v___x_1898_,
                                        v___x_1899_,
                                        v___x_1900_,
                                        v___x_1903_,
                                    );
                                    lean_inc(v___x_1894_);
                                    v___y_1735_ = v___x_1894_;
                                    v___y_1736_ = v_v_1889_;
                                    v___y_1737_ = v___x_1904_;
                                    state = 14;
                                    continue;
                                } else {
                                    v___x_1905_ = l_Int_toNat(v___x_1895_);
                                    lean_dec(v___x_1895_);
                                    v___x_1906_ = l_Lean_instToExprInt_mkNat(v___x_1905_);
                                    lean_inc(v___x_1894_);
                                    v___y_1735_ = v___x_1894_;
                                    v___y_1736_ = v_v_1889_;
                                    v___y_1737_ = v___x_1906_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_1666_);
                                v_k_1907_ = lean_ctor_get(v_p_1890_, 0);
                                lean_inc(v_k_1907_);
                                v_v_1908_ = lean_ctor_get(v_p_1890_, 1);
                                lean_inc(v_v_1908_);
                                v_p_1909_ = lean_ctor_get(v_p_1890_, 2);
                                lean_inc_ref(v_p_1909_);
                                lean_dec_ref_known(v_p_1890_, 3);
                                v___x_1910_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31,
                                );
                                v___x_1911_ = lean_int_dec_eq(v_k_1907_, v___x_1910_);
                                lean_dec(v_k_1907_);
                                if v___x_1911_ == 0 {
                                    lean_dec_ref(v_p_1909_);
                                    lean_dec(v_v_1908_);
                                    lean_dec(v_v_1889_);
                                    v___y_1774_ = v_a_1658_;
                                    v___y_1775_ = v_a_1659_;
                                    v___y_1776_ = v_a_1660_;
                                    v___y_1777_ = v_a_1661_;
                                    state = 20;
                                    continue;
                                } else {
                                    if lean_obj_tag(v_p_1909_) == 0 {
                                        v_k_1912_ = lean_ctor_get(v_p_1909_, 0);
                                        v_isSharedCheck_1956_ =
                                            (!lean_is_exclusive(v_p_1909_)) as u8;
                                        if v_isSharedCheck_1956_ == 0 {
                                            v___x_1914_ = v_p_1909_;
                                            v_isShared_1915_ = v_isSharedCheck_1956_;
                                            state = 34;
                                            continue;
                                        } else {
                                            lean_inc(v_k_1912_);
                                            lean_dec(v_p_1909_);
                                            v___x_1914_ = lean_box(0);
                                            v_isShared_1915_ = v_isSharedCheck_1956_;
                                            state = 34;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_p_1909_);
                                        lean_dec(v_v_1908_);
                                        lean_dec(v_v_1889_);
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
                        lean_del_object(v___x_1666_);
                        v___y_1774_ = v_a_1658_;
                        v___y_1775_ = v_a_1659_;
                        v___y_1776_ = v_a_1660_;
                        v___y_1777_ = v_a_1661_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1772_);
                    lean_dec_ref(v___x_1694_);
                    lean_del_object(v___x_1692_);
                    lean_del_object(v___x_1687_);
                    lean_dec_ref(v___f_1683_);
                    lean_del_object(v___x_1680_);
                    lean_dec(v_snd_1678_);
                    lean_dec(v_fst_1677_);
                    lean_del_object(v___x_1675_);
                    lean_dec(v_fst_1673_);
                    lean_del_object(v___x_1670_);
                    lean_del_object(v___x_1666_);
                    v___x_1957_ = lean_box(0);
                    v___x_1958_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1958_, 0, v___x_1957_);
                    return v___x_1958_;
                }
            }
            34 => {
                v___x_1916_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
                );
                v___x_1917_ = lean_int_dec_eq(v_k_1912_, v___x_1916_);
                lean_dec(v_k_1912_);
                if v___x_1917_ == 0 {
                    lean_del_object(v___x_1914_);
                    lean_dec(v_v_1908_);
                    lean_dec(v_v_1889_);
                    v___y_1774_ = v_a_1658_;
                    v___y_1775_ = v_a_1659_;
                    v___y_1776_ = v_a_1660_;
                    v___y_1777_ = v_a_1661_;
                    state = 20;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_1772_, 3);
                    lean_del_object(v___x_1692_);
                    lean_del_object(v___x_1687_);
                    lean_dec_ref(v___f_1683_);
                    lean_del_object(v___x_1680_);
                    lean_del_object(v___x_1675_);
                    lean_del_object(v___x_1670_);
                    v___x_1918_ = lean_array_get_borrowed(v___x_1682_, v_snd_1678_, v_v_1889_);
                    v___x_1919_ = lean_array_get_borrowed(v___x_1682_, v_snd_1678_, v_v_1908_);
                    lean_inc(v___x_1919_);
                    lean_inc(v___x_1918_);
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
                        if lean_obj_tag(v___x_1922_) == 0 {
                            v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
                            v_isSharedCheck_1943_ = (!lean_is_exclusive(v___x_1922_)) as u8;
                            if v_isSharedCheck_1943_ == 0 {
                                v___x_1925_ = v___x_1922_;
                                v_isShared_1926_ = v_isSharedCheck_1943_;
                                state = 35;
                                continue;
                            } else {
                                lean_inc(v_a_1923_);
                                lean_dec(v___x_1922_);
                                v___x_1925_ = lean_box(0);
                                v_isShared_1926_ = v_isSharedCheck_1943_;
                                state = 35;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_1920_);
                            lean_del_object(v___x_1914_);
                            lean_dec(v_v_1908_);
                            lean_dec(v_v_1889_);
                            lean_dec_ref(v___x_1694_);
                            lean_dec(v_fst_1677_);
                            lean_dec(v_fst_1673_);
                            v_a_1944_ = lean_ctor_get(v___x_1922_, 0);
                            v_isSharedCheck_1951_ = (!lean_is_exclusive(v___x_1922_)) as u8;
                            if v_isSharedCheck_1951_ == 0 {
                                v___x_1946_ = v___x_1922_;
                                v_isShared_1947_ = v_isSharedCheck_1951_;
                                state = 38;
                                continue;
                            } else {
                                lean_inc(v_a_1944_);
                                lean_dec(v___x_1922_);
                                v___x_1946_ = lean_box(0);
                                v_isShared_1947_ = v_isSharedCheck_1951_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_1920_);
                        lean_dec(v_v_1908_);
                        lean_dec(v_v_1889_);
                        lean_dec_ref(v___x_1694_);
                        lean_dec(v_snd_1678_);
                        lean_dec(v_fst_1677_);
                        lean_dec(v_fst_1673_);
                        v___x_1952_ = lean_box(0);
                        if v_isShared_1915_ == 0 {
                            lean_ctor_set(v___x_1914_, 0, v___x_1952_);
                            v___x_1954_ = v___x_1914_;
                            state = 40;
                            continue;
                        } else {
                            v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
                            v___x_1954_ = v_reuseFailAlloc_1955_;
                            state = 40;
                            continue;
                        }
                    }
                }
            }
            35 => {
                v___x_1927_ = lean_obj_once(
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
                lean_inc_ref(v___x_1920_);
                v___x_1934_ = l_Lean_mkPropEq(v___x_1694_, v___x_1920_);
                v___x_1935_ = l_Lean_Meta_mkExpectedPropHint(v___x_1933_, v___x_1934_);
                v___x_1936_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1936_, 0, v___x_1920_);
                lean_ctor_set(v___x_1936_, 1, v___x_1935_);
                if v_isShared_1915_ == 0 {
                    lean_ctor_set_tag(v___x_1914_, 1);
                    lean_ctor_set(v___x_1914_, 0, v___x_1936_);
                    v___x_1938_ = v___x_1914_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1936_);
                    v___x_1938_ = v_reuseFailAlloc_1942_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_1926_ == 0 {
                    lean_ctor_set(v___x_1925_, 0, v___x_1938_);
                    v___x_1940_ = v___x_1925_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
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
                    v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
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
                v___x_1970_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38,
                );
                v___x_1971_ = lean_obj_once(
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
                v___x_1978_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1978_, 0, v___x_1970_);
                lean_ctor_set(v___x_1978_, 1, v___x_1977_);
                v___x_1979_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1979_, 0, v___x_1978_);
                if v_isShared_1969_ == 0 {
                    lean_ctor_set(v___x_1968_, 0, v___x_1979_);
                    v___x_1981_ = v___x_1968_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
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
                    v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
                    v___x_1989_ = v_reuseFailAlloc_1990_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_1989_;
            }
            45 => {
                v___x_1997_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8,
                );
                v___x_1998_ = lean_obj_once(
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
                v___x_2005_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2005_, 0, v___x_1997_);
                lean_ctor_set(v___x_2005_, 1, v___x_2004_);
                v___x_2006_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2006_, 0, v___x_2005_);
                if v_isShared_1996_ == 0 {
                    lean_ctor_set(v___x_1995_, 0, v___x_2006_);
                    v___x_2008_ = v___x_1995_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
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
                    v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
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
                    v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
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
                    v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
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
                    v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
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
    mut v_e_2053_: *mut LeanObject,
    mut v_a_2054_: *mut LeanObject,
    mut v_a_2055_: *mut LeanObject,
    mut v_a_2056_: *mut LeanObject,
    mut v_a_2057_: *mut LeanObject,
    mut v_a_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2059_: *mut LeanObject = core::ptr::null_mut();
    v_res_2059_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(
        v_e_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_,
    );
    lean_dec(v_a_2057_);
    lean_dec_ref(v_a_2056_);
    lean_dec(v_a_2055_);
    lean_dec_ref(v_a_2054_);
    return v_res_2059_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    v___x_2065_ = lean_box(0);
    v___x_2066_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1;
    v___x_2067_ = l_Lean_mkConst(v___x_2066_, v___x_2065_);
    return v___x_2067_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5() -> *mut LeanObject {
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    v___x_2073_ = lean_box(0);
    v___x_2074_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4;
    v___x_2075_ = l_Lean_mkConst(v___x_2074_, v___x_2073_);
    return v___x_2075_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8() -> *mut LeanObject {
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    v___x_2081_ = lean_box(0);
    v___x_2082_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7;
    v___x_2083_ = l_Lean_mkConst(v___x_2082_, v___x_2081_);
    return v___x_2083_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11() -> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    v___x_2089_ = lean_box(0);
    v___x_2090_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10;
    v___x_2091_ = l_Lean_mkConst(v___x_2090_, v___x_2089_);
    return v___x_2091_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14() -> *mut LeanObject {
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    v___x_2097_ = lean_box(0);
    v___x_2098_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13;
    v___x_2099_ = l_Lean_mkConst(v___x_2098_, v___x_2097_);
    return v___x_2099_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(
    mut v_e_2105_: *mut LeanObject,
    mut v_checkIfModified_2106_: u8,
    mut v_a_2107_: *mut LeanObject,
    mut v_a_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: u8 = 0;
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2214_: u8 = 0;
    let mut v_a_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut v___y_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v_a_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v_a_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2281_: u8 = 0;
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2286_: u8 = 0;
    let mut v_val_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v_snd_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v_fst_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___f_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2345_: u8 = 0;
    let mut v_a_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2353_: u8 = 0;
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut v_a_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2384_: u8 = 0;
    let mut v_reuseFailAlloc_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2386_: u8 = 0;
    let mut v_a_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_a_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2398_: u8 = 0;
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2402_: u8 = 0;
    let mut v_isSharedCheck_2403_: u8 = 0;
    let mut v_isSharedCheck_2404_: u8 = 0;
    let mut v_isSharedCheck_2405_: u8 = 0;
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_a_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2418_: u8 = 0;
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
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
                lean_inc_ref(v___y_2113_);
                v___x_2116_ = l_Lean_mkPropEq(v___y_2114_, v___y_2113_);
                v___x_2117_ = l_Lean_Meta_mkExpectedPropHint(v_h_2115_, v___x_2116_);
                v___x_2118_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2118_, 0, v___y_2113_);
                lean_ctor_set(v___x_2118_, 1, v___x_2117_);
                v___x_2119_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2119_, 0, v___x_2118_);
                v___x_2120_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2120_, 0, v___x_2119_);
                return v___x_2120_;
            }
            2 => {
                v___x_2130_ = l_Lean_eagerReflBoolTrue;
                lean_inc_ref(v___y_2125_);
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
                lean_inc_ref(v___y_2133_);
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
                lean_inc_ref(v___x_2154_);
                v___x_2155_ = l_Int_Linear_Poly_denoteExpr___redArg(v___y_2151_, v___x_2154_);
                if lean_obj_tag(v___x_2155_) == 0 {
                    v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
                    lean_inc(v_a_2156_);
                    lean_dec_ref_known(v___x_2155_, 1);
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
                        if lean_obj_tag(v___x_2159_) == 0 {
                            v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
                            lean_inc(v_a_2160_);
                            lean_dec_ref_known(v___x_2159_, 1);
                            v___x_2161_ = lean_box(0);
                            v___x_2162_ = lean_obj_once(
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
                                v___x_2169_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_2169_, 0, v___x_2168_);
                                lean_ctor_set(v___x_2169_, 1, v___x_2161_);
                                v___x_2170_ =
                                    l_Lean_Expr_const___override(v___x_2167_, v___x_2169_);
                                v___x_2171_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                );
                                v___x_2172_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                );
                                v___x_2173_ = lean_int_neg(v___y_2145_);
                                lean_dec(v___y_2145_);
                                v___x_2174_ = l_Int_toNat(v___x_2173_);
                                lean_dec(v___x_2173_);
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
                                lean_dec(v___y_2145_);
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
                            lean_dec_ref(v___x_2158_);
                            lean_dec_ref(v___x_2154_);
                            lean_dec_ref(v___y_2152_);
                            lean_dec_ref(v___y_2149_);
                            lean_dec_ref(v___y_2146_);
                            lean_dec(v___y_2145_);
                            v_a_2179_ = lean_ctor_get(v___x_2159_, 0);
                            v_isSharedCheck_2186_ = (!lean_is_exclusive(v___x_2159_)) as u8;
                            if v_isSharedCheck_2186_ == 0 {
                                v___x_2181_ = v___x_2159_;
                                v_isShared_2182_ = v_isSharedCheck_2186_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2179_);
                                lean_dec(v___x_2159_);
                                v___x_2181_ = lean_box(0);
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
                        if lean_obj_tag(v___x_2187_) == 0 {
                            v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
                            lean_inc(v_a_2188_);
                            lean_dec_ref_known(v___x_2187_, 1);
                            v___x_2189_ = lean_box(0);
                            v___x_2190_ = lean_obj_once(
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
                                v___x_2197_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_2197_, 0, v___x_2196_);
                                lean_ctor_set(v___x_2197_, 1, v___x_2189_);
                                v___x_2198_ =
                                    l_Lean_Expr_const___override(v___x_2195_, v___x_2197_);
                                v___x_2199_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                );
                                v___x_2200_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                );
                                v___x_2201_ = lean_int_neg(v___y_2145_);
                                lean_dec(v___y_2145_);
                                v___x_2202_ = l_Int_toNat(v___x_2201_);
                                lean_dec(v___x_2201_);
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
                                lean_dec(v___y_2145_);
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
                            lean_dec_ref(v___x_2158_);
                            lean_dec_ref(v___x_2154_);
                            lean_dec_ref(v___y_2152_);
                            lean_dec_ref(v___y_2149_);
                            lean_dec_ref(v___y_2146_);
                            lean_dec(v___y_2145_);
                            v_a_2207_ = lean_ctor_get(v___x_2187_, 0);
                            v_isSharedCheck_2214_ = (!lean_is_exclusive(v___x_2187_)) as u8;
                            if v_isSharedCheck_2214_ == 0 {
                                v___x_2209_ = v___x_2187_;
                                v_isShared_2210_ = v_isSharedCheck_2214_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2207_);
                                lean_dec(v___x_2187_);
                                v___x_2209_ = lean_box(0);
                                v_isShared_2210_ = v_isSharedCheck_2214_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2154_);
                    lean_dec_ref(v___y_2152_);
                    lean_dec_ref(v___y_2150_);
                    lean_dec_ref(v___y_2149_);
                    lean_dec_ref(v___y_2146_);
                    lean_dec(v___y_2145_);
                    v_a_2215_ = lean_ctor_get(v___x_2155_, 0);
                    v_isSharedCheck_2222_ = (!lean_is_exclusive(v___x_2155_)) as u8;
                    if v_isSharedCheck_2222_ == 0 {
                        v___x_2217_ = v___x_2155_;
                        v_isShared_2218_ = v_isSharedCheck_2222_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2215_);
                        lean_dec(v___x_2155_);
                        v___x_2217_ = lean_box(0);
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
                    v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
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
                    v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
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
                    v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
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
                v___x_2231_ = lean_unsigned_to_nat(1);
                v___x_2232_ = lean_nat_dec_eq(v___x_2230_, v___x_2231_);
                if v___x_2232_ == 0 {
                    v___x_2233_ = l_Int_Linear_Poly_getConst(v___y_2225_);
                    v___x_2234_ = lean_nat_to_int(v___x_2230_);
                    v___x_2235_ = lean_int_emod(v___x_2233_, v___x_2234_);
                    lean_dec(v___x_2233_);
                    v___x_2236_ = lean_unsigned_to_nat(0);
                    v___x_2237_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
                    );
                    v___x_2238_ = lean_int_dec_eq(v___x_2235_, v___x_2237_);
                    lean_dec(v___x_2235_);
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
                    lean_dec(v___x_2230_);
                    lean_inc_ref(v___y_2225_);
                    v___x_2240_ = l_Int_Linear_Poly_denoteExpr___redArg(v___y_2228_, v___y_2225_);
                    if lean_obj_tag(v___x_2240_) == 0 {
                        v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
                        lean_inc(v_a_2241_);
                        lean_dec_ref_known(v___x_2240_, 1);
                        v___x_2242_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v___y_2227_,
                            v_a_2107_,
                            v_a_2108_,
                            v_a_2109_,
                            v_a_2110_,
                        );
                        if lean_obj_tag(v___x_2242_) == 0 {
                            v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
                            v_isSharedCheck_2262_ = (!lean_is_exclusive(v___x_2242_)) as u8;
                            if v_isSharedCheck_2262_ == 0 {
                                v___x_2245_ = v___x_2242_;
                                v_isShared_2246_ = v_isSharedCheck_2262_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_2243_);
                                lean_dec(v___x_2242_);
                                v___x_2245_ = lean_box(0);
                                v_isShared_2246_ = v_isSharedCheck_2262_;
                                state = 12;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2241_);
                            lean_dec_ref(v___y_2229_);
                            lean_dec_ref(v___y_2226_);
                            lean_dec_ref(v___y_2225_);
                            lean_dec_ref(v___y_2224_);
                            v_a_2263_ = lean_ctor_get(v___x_2242_, 0);
                            v_isSharedCheck_2270_ = (!lean_is_exclusive(v___x_2242_)) as u8;
                            if v_isSharedCheck_2270_ == 0 {
                                v___x_2265_ = v___x_2242_;
                                v_isShared_2266_ = v_isSharedCheck_2270_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_2263_);
                                lean_dec(v___x_2242_);
                                v___x_2265_ = lean_box(0);
                                v_isShared_2266_ = v_isSharedCheck_2270_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_2229_);
                        lean_dec_ref(v___y_2227_);
                        lean_dec_ref(v___y_2226_);
                        lean_dec_ref(v___y_2225_);
                        lean_dec_ref(v___y_2224_);
                        v_a_2271_ = lean_ctor_get(v___x_2240_, 0);
                        v_isSharedCheck_2278_ = (!lean_is_exclusive(v___x_2240_)) as u8;
                        if v_isSharedCheck_2278_ == 0 {
                            v___x_2273_ = v___x_2240_;
                            v_isShared_2274_ = v_isSharedCheck_2278_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_2271_);
                            lean_dec(v___x_2240_);
                            v___x_2273_ = lean_box(0);
                            v_isShared_2274_ = v_isSharedCheck_2278_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___x_2247_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23,
                );
                v___x_2248_ = l_Lean_mkIntLE(v_a_2241_, v___x_2247_);
                v___x_2249_ = lean_obj_once(
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
                lean_inc_ref(v___x_2248_);
                v___x_2255_ = l_Lean_mkPropEq(v___y_2229_, v___x_2248_);
                v___x_2256_ = l_Lean_Meta_mkExpectedPropHint(v___x_2254_, v___x_2255_);
                v___x_2257_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2257_, 0, v___x_2248_);
                lean_ctor_set(v___x_2257_, 1, v___x_2256_);
                v___x_2258_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2258_, 0, v___x_2257_);
                if v_isShared_2246_ == 0 {
                    lean_ctor_set(v___x_2245_, 0, v___x_2258_);
                    v___x_2260_ = v___x_2245_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
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
                    v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
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
                    v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
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
                if lean_obj_tag(v___x_2282_) == 0 {
                    v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
                    v_isSharedCheck_2410_ = (!lean_is_exclusive(v___x_2282_)) as u8;
                    if v_isSharedCheck_2410_ == 0 {
                        v___x_2285_ = v___x_2282_;
                        v_isShared_2286_ = v_isSharedCheck_2410_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_2283_);
                        lean_dec(v___x_2282_);
                        v___x_2285_ = lean_box(0);
                        v_isShared_2286_ = v_isSharedCheck_2410_;
                        state = 19;
                        continue;
                    }
                } else {
                    v_a_2411_ = lean_ctor_get(v___x_2282_, 0);
                    v_isSharedCheck_2418_ = (!lean_is_exclusive(v___x_2282_)) as u8;
                    if v_isSharedCheck_2418_ == 0 {
                        v___x_2413_ = v___x_2282_;
                        v_isShared_2414_ = v_isSharedCheck_2418_;
                        state = 43;
                        continue;
                    } else {
                        lean_inc(v_a_2411_);
                        lean_dec(v___x_2282_);
                        v___x_2413_ = lean_box(0);
                        v_isShared_2414_ = v_isSharedCheck_2418_;
                        state = 43;
                        continue;
                    }
                }
            }
            19 => {
                if lean_obj_tag(v_a_2283_) == 1 {
                    lean_del_object(v___x_2285_);
                    v_val_2287_ = lean_ctor_get(v_a_2283_, 0);
                    v_isSharedCheck_2405_ = (!lean_is_exclusive(v_a_2283_)) as u8;
                    if v_isSharedCheck_2405_ == 0 {
                        v___x_2289_ = v_a_2283_;
                        v_isShared_2290_ = v_isSharedCheck_2405_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_val_2287_);
                        lean_dec(v_a_2283_);
                        v___x_2289_ = lean_box(0);
                        v_isShared_2290_ = v_isSharedCheck_2405_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2283_);
                    v___x_2406_ = lean_box(0);
                    if v_isShared_2286_ == 0 {
                        lean_ctor_set(v___x_2285_, 0, v___x_2406_);
                        v___x_2408_ = v___x_2285_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
                        v___x_2408_ = v_reuseFailAlloc_2409_;
                        state = 42;
                        continue;
                    }
                }
            }
            20 => {
                v_snd_2291_ = lean_ctor_get(v_val_2287_, 1);
                v_fst_2292_ = lean_ctor_get(v_val_2287_, 0);
                v_isSharedCheck_2404_ = (!lean_is_exclusive(v_val_2287_)) as u8;
                if v_isSharedCheck_2404_ == 0 {
                    v___x_2294_ = v_val_2287_;
                    v_isShared_2295_ = v_isSharedCheck_2404_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_snd_2291_);
                    lean_inc(v_fst_2292_);
                    lean_dec(v_val_2287_);
                    v___x_2294_ = lean_box(0);
                    v_isShared_2295_ = v_isSharedCheck_2404_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v_fst_2296_ = lean_ctor_get(v_snd_2291_, 0);
                v_snd_2297_ = lean_ctor_get(v_snd_2291_, 1);
                v_isSharedCheck_2403_ = (!lean_is_exclusive(v_snd_2291_)) as u8;
                if v_isSharedCheck_2403_ == 0 {
                    v___x_2299_ = v_snd_2291_;
                    v_isShared_2300_ = v_isSharedCheck_2403_;
                    state = 22;
                    continue;
                } else {
                    lean_inc(v_snd_2297_);
                    lean_inc(v_fst_2296_);
                    lean_dec(v_snd_2291_);
                    v___x_2299_ = lean_box(0);
                    v_isShared_2300_ = v_isSharedCheck_2403_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                lean_inc(v_snd_2297_);
                v___f_2301_ = lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2301_, 0, v___x_2279_);
                lean_closure_set(v___f_2301_, 1, v_snd_2297_);
                lean_inc(v_fst_2292_);
                lean_inc_ref(v___f_2301_);
                v___x_2302_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_2301_, v_fst_2292_);
                if lean_obj_tag(v___x_2302_) == 0 {
                    v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
                    lean_inc(v_a_2303_);
                    lean_dec_ref_known(v___x_2302_, 1);
                    lean_inc(v_fst_2296_);
                    lean_inc_ref(v___f_2301_);
                    v___x_2304_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_2301_, v_fst_2296_);
                    if lean_obj_tag(v___x_2304_) == 0 {
                        v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
                        v_isSharedCheck_2386_ = (!lean_is_exclusive(v___x_2304_)) as u8;
                        if v_isSharedCheck_2386_ == 0 {
                            v___x_2307_ = v___x_2304_;
                            v_isShared_2308_ = v_isSharedCheck_2386_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_2305_);
                            lean_dec(v___x_2304_);
                            v___x_2307_ = lean_box(0);
                            v_isShared_2308_ = v_isSharedCheck_2386_;
                            state = 23;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2303_);
                        lean_dec_ref(v___f_2301_);
                        lean_del_object(v___x_2299_);
                        lean_dec(v_snd_2297_);
                        lean_dec(v_fst_2296_);
                        lean_del_object(v___x_2294_);
                        lean_dec(v_fst_2292_);
                        lean_del_object(v___x_2289_);
                        v_a_2387_ = lean_ctor_get(v___x_2304_, 0);
                        v_isSharedCheck_2394_ = (!lean_is_exclusive(v___x_2304_)) as u8;
                        if v_isSharedCheck_2394_ == 0 {
                            v___x_2389_ = v___x_2304_;
                            v_isShared_2390_ = v_isSharedCheck_2394_;
                            state = 38;
                            continue;
                        } else {
                            lean_inc(v_a_2387_);
                            lean_dec(v___x_2304_);
                            v___x_2389_ = lean_box(0);
                            v_isShared_2390_ = v_isSharedCheck_2394_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___f_2301_);
                    lean_del_object(v___x_2299_);
                    lean_dec(v_snd_2297_);
                    lean_dec(v_fst_2296_);
                    lean_del_object(v___x_2294_);
                    lean_dec(v_fst_2292_);
                    lean_del_object(v___x_2289_);
                    v_a_2395_ = lean_ctor_get(v___x_2302_, 0);
                    v_isSharedCheck_2402_ = (!lean_is_exclusive(v___x_2302_)) as u8;
                    if v_isSharedCheck_2402_ == 0 {
                        v___x_2397_ = v___x_2302_;
                        v_isShared_2398_ = v_isSharedCheck_2402_;
                        state = 40;
                        continue;
                    } else {
                        lean_inc(v_a_2395_);
                        lean_dec(v___x_2302_);
                        v___x_2397_ = lean_box(0);
                        v_isShared_2398_ = v_isSharedCheck_2402_;
                        state = 40;
                        continue;
                    }
                }
            }
            23 => {
                v___x_2309_ = l_Lean_mkIntLE(v_a_2303_, v_a_2305_);
                lean_inc(v_fst_2296_);
                lean_inc(v_fst_2292_);
                if v_isShared_2295_ == 0 {
                    lean_ctor_set_tag(v___x_2294_, 3);
                    lean_ctor_set(v___x_2294_, 1, v_fst_2296_);
                    v___x_2311_ = v___x_2294_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2385_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_fst_2292_);
                    lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_fst_2296_);
                    v___x_2311_ = v_reuseFailAlloc_2385_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_2312_ = l_Int_Linear_Expr_norm(v___x_2311_);
                lean_dec_ref(v___x_2311_);
                v___x_2313_ = l_Int_Linear_Poly_isUnsatLe(v___x_2312_);
                if v___x_2313_ == 0 {
                    v___x_2314_ = l_Int_Linear_Poly_isValidLe(v___x_2312_);
                    if v___x_2314_ == 0 {
                        lean_del_object(v___x_2299_);
                        lean_del_object(v___x_2289_);
                        if v___y_2281_ == 0 {
                            lean_del_object(v___x_2307_);
                            v___y_2224_ = v_fst_2296_;
                            v___y_2225_ = v___x_2312_;
                            v___y_2226_ = v_fst_2292_;
                            v___y_2227_ = v_snd_2297_;
                            v___y_2228_ = v___f_2301_;
                            v___y_2229_ = v___x_2309_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc_ref(v___x_2312_);
                            v___x_2315_ = l_Int_Linear_Poly_toExpr(v___x_2312_);
                            v___x_2316_ = l_Int_Linear_instBEqExpr_beq(v___x_2315_, v_fst_2292_);
                            lean_dec_ref(v___x_2315_);
                            if v___x_2316_ == 0 {
                                lean_del_object(v___x_2307_);
                                v___y_2224_ = v_fst_2296_;
                                v___y_2225_ = v___x_2312_;
                                v___y_2226_ = v_fst_2292_;
                                v___y_2227_ = v_snd_2297_;
                                v___y_2228_ = v___f_2301_;
                                v___y_2229_ = v___x_2309_;
                                state = 11;
                                continue;
                            } else {
                                v___x_2317_ = lean_obj_once(
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
                                    lean_del_object(v___x_2307_);
                                    v___y_2224_ = v_fst_2296_;
                                    v___y_2225_ = v___x_2312_;
                                    v___y_2226_ = v_fst_2292_;
                                    v___y_2227_ = v_snd_2297_;
                                    v___y_2228_ = v___f_2301_;
                                    v___y_2229_ = v___x_2309_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_dec_ref(v___x_2312_);
                                    lean_dec_ref(v___x_2309_);
                                    lean_dec_ref(v___f_2301_);
                                    lean_dec(v_snd_2297_);
                                    lean_dec(v_fst_2296_);
                                    lean_dec(v_fst_2292_);
                                    v___x_2319_ = lean_box(0);
                                    if v_isShared_2308_ == 0 {
                                        lean_ctor_set(v___x_2307_, 0, v___x_2319_);
                                        v___x_2321_ = v___x_2307_;
                                        state = 25;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
                                        v___x_2321_ = v_reuseFailAlloc_2322_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2312_);
                        lean_del_object(v___x_2307_);
                        lean_dec_ref(v___f_2301_);
                        v___x_2323_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                            v_snd_2297_,
                            v_a_2107_,
                            v_a_2108_,
                            v_a_2109_,
                            v_a_2110_,
                        );
                        if lean_obj_tag(v___x_2323_) == 0 {
                            v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
                            v_isSharedCheck_2345_ = (!lean_is_exclusive(v___x_2323_)) as u8;
                            if v_isSharedCheck_2345_ == 0 {
                                v___x_2326_ = v___x_2323_;
                                v_isShared_2327_ = v_isSharedCheck_2345_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_a_2324_);
                                lean_dec(v___x_2323_);
                                v___x_2326_ = lean_box(0);
                                v_isShared_2327_ = v_isSharedCheck_2345_;
                                state = 26;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_2309_);
                            lean_del_object(v___x_2299_);
                            lean_dec(v_fst_2296_);
                            lean_dec(v_fst_2292_);
                            lean_del_object(v___x_2289_);
                            v_a_2346_ = lean_ctor_get(v___x_2323_, 0);
                            v_isSharedCheck_2353_ = (!lean_is_exclusive(v___x_2323_)) as u8;
                            if v_isSharedCheck_2353_ == 0 {
                                v___x_2348_ = v___x_2323_;
                                v_isShared_2349_ = v_isSharedCheck_2353_;
                                state = 30;
                                continue;
                            } else {
                                lean_inc(v_a_2346_);
                                lean_dec(v___x_2323_);
                                v___x_2348_ = lean_box(0);
                                v_isShared_2349_ = v_isSharedCheck_2353_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2312_);
                    lean_del_object(v___x_2307_);
                    lean_dec_ref(v___f_2301_);
                    v___x_2354_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_2297_,
                        v_a_2107_,
                        v_a_2108_,
                        v_a_2109_,
                        v_a_2110_,
                    );
                    if lean_obj_tag(v___x_2354_) == 0 {
                        v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
                        v_isSharedCheck_2376_ = (!lean_is_exclusive(v___x_2354_)) as u8;
                        if v_isSharedCheck_2376_ == 0 {
                            v___x_2357_ = v___x_2354_;
                            v_isShared_2358_ = v_isSharedCheck_2376_;
                            state = 32;
                            continue;
                        } else {
                            lean_inc(v_a_2355_);
                            lean_dec(v___x_2354_);
                            v___x_2357_ = lean_box(0);
                            v_isShared_2358_ = v_isSharedCheck_2376_;
                            state = 32;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_2309_);
                        lean_del_object(v___x_2299_);
                        lean_dec(v_fst_2296_);
                        lean_dec(v_fst_2292_);
                        lean_del_object(v___x_2289_);
                        v_a_2377_ = lean_ctor_get(v___x_2354_, 0);
                        v_isSharedCheck_2384_ = (!lean_is_exclusive(v___x_2354_)) as u8;
                        if v_isSharedCheck_2384_ == 0 {
                            v___x_2379_ = v___x_2354_;
                            v_isShared_2380_ = v_isSharedCheck_2384_;
                            state = 36;
                            continue;
                        } else {
                            lean_inc(v_a_2377_);
                            lean_dec(v___x_2354_);
                            v___x_2379_ = lean_box(0);
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
                v___x_2328_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38,
                );
                v___x_2329_ = lean_obj_once(
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
                    lean_ctor_set(v___x_2299_, 1, v___x_2335_);
                    lean_ctor_set(v___x_2299_, 0, v___x_2328_);
                    v___x_2337_ = v___x_2299_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2328_);
                    lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2335_);
                    v___x_2337_ = v_reuseFailAlloc_2344_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2290_ == 0 {
                    lean_ctor_set(v___x_2289_, 0, v___x_2337_);
                    v___x_2339_ = v___x_2289_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2337_);
                    v___x_2339_ = v_reuseFailAlloc_2343_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2327_ == 0 {
                    lean_ctor_set(v___x_2326_, 0, v___x_2339_);
                    v___x_2341_ = v___x_2326_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
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
                    v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
                    v___x_2351_ = v_reuseFailAlloc_2352_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2351_;
            }
            32 => {
                v___x_2359_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8,
                );
                v___x_2360_ = lean_obj_once(
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
                    lean_ctor_set(v___x_2299_, 1, v___x_2366_);
                    lean_ctor_set(v___x_2299_, 0, v___x_2359_);
                    v___x_2368_ = v___x_2299_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2359_);
                    lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2366_);
                    v___x_2368_ = v_reuseFailAlloc_2375_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                if v_isShared_2290_ == 0 {
                    lean_ctor_set(v___x_2289_, 0, v___x_2368_);
                    v___x_2370_ = v___x_2289_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2368_);
                    v___x_2370_ = v_reuseFailAlloc_2374_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_2358_ == 0 {
                    lean_ctor_set(v___x_2357_, 0, v___x_2370_);
                    v___x_2372_ = v___x_2357_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
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
                    v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
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
                    v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
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
                    v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
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
                    v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
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
    mut v_e_2421_: *mut LeanObject,
    mut v_checkIfModified_2422_: *mut LeanObject,
    mut v_a_2423_: *mut LeanObject,
    mut v_a_2424_: *mut LeanObject,
    mut v_a_2425_: *mut LeanObject,
    mut v_a_2426_: *mut LeanObject,
    mut v_a_2427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkIfModified_boxed_2428_: u8 = 0;
    let mut v_res_2429_: *mut LeanObject = core::ptr::null_mut();
    v_checkIfModified_boxed_2428_ = (lean_unbox(v_checkIfModified_2422_) as u8);
    v_res_2429_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(
        v_e_2421_,
        v_checkIfModified_boxed_2428_,
        v_a_2423_,
        v_a_2424_,
        v_a_2425_,
        v_a_2426_,
    );
    lean_dec(v_a_2426_);
    lean_dec_ref(v_a_2425_);
    lean_dec(v_a_2424_);
    lean_dec_ref(v_a_2423_);
    return v_res_2429_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    v___x_2435_ = lean_box(0);
    v___x_2436_ = l_Lean_Level_succ___override(v___x_2435_);
    return v___x_2436_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    v___x_2437_ = lean_box(0);
    v___x_2438_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3,
    );
    v___x_2439_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2439_, 0, v___x_2438_);
    lean_ctor_set(v___x_2439_, 1, v___x_2437_);
    return v___x_2439_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5() -> *mut LeanObject {
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    v___x_2440_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4,
    );
    v___x_2441_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2;
    v___x_2442_ = l_Lean_mkConst(v___x_2441_, v___x_2440_);
    return v___x_2442_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6() -> *mut LeanObject {
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    v___x_2443_ = lean_box(0);
    v___x_2444_ = l_Lean_mkSort(v___x_2443_);
    return v___x_2444_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18() -> *mut LeanObject {
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    v___x_2463_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once),
        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30,
    );
    v___x_2464_ = l_Lean_mkIntLit(v___x_2463_);
    return v___x_2464_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21() -> *mut LeanObject {
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    v___x_2469_ = lean_box(0);
    v___x_2470_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
    v___x_2471_ = l_Lean_mkConst(v___x_2470_, v___x_2469_);
    return v___x_2471_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24() -> *mut LeanObject {
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    v___x_2476_ = lean_box(0);
    v___x_2477_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23;
    v___x_2478_ = l_Lean_mkConst(v___x_2477_, v___x_2476_);
    return v___x_2478_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27() -> *mut LeanObject {
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    v___x_2483_ = lean_box(0);
    v___x_2484_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
    v___x_2485_ = l_Lean_mkConst(v___x_2484_, v___x_2483_);
    return v___x_2485_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30() -> *mut LeanObject {
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    v___x_2490_ = lean_box(0);
    v___x_2491_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29;
    v___x_2492_ = l_Lean_mkConst(v___x_2491_, v___x_2490_);
    return v___x_2492_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(
    mut v_e_2493_: *mut LeanObject,
    mut v_a_2494_: *mut LeanObject,
    mut v_a_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_u2081_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v_val_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v_fst_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2523_: u8 = 0;
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2536_: u8 = 0;
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2543_: u8 = 0;
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: u8 = 0;
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: u8 = 0;
    let mut v_arg_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: u8 = 0;
    let mut v_arg_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    let mut v_arg_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: u8 = 0;
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u8 = 0;
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: u8 = 0;
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2603_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2623_: u8 = 0;
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2639_: u8 = 0;
    let mut v_a_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2544_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8;
                v___x_2545_ = lean_unsigned_to_nat(1);
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
                    if lean_obj_tag(v___x_2550_) == 0 {
                        v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
                        lean_inc(v_a_2551_);
                        lean_dec_ref_known(v___x_2550_, 1);
                        v___x_2552_ = l_Lean_Expr_cleanupAnnotations(v_a_2551_);
                        v___x_2553_ = l_Lean_Expr_isApp(v___x_2552_);
                        if v___x_2553_ == 0 {
                            lean_dec_ref(v___x_2552_);
                            lean_dec_ref(v_e_2493_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_2554_ = lean_ctor_get(v___x_2552_, 1);
                            lean_inc_ref(v_arg_2554_);
                            v___x_2555_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2552_);
                            v___x_2556_ = l_Lean_Expr_isApp(v___x_2555_);
                            if v___x_2556_ == 0 {
                                lean_dec_ref(v___x_2555_);
                                lean_dec_ref(v_arg_2554_);
                                lean_dec_ref(v_e_2493_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_2557_ = lean_ctor_get(v___x_2555_, 1);
                                lean_inc_ref(v_arg_2557_);
                                v___x_2558_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2555_);
                                v___x_2559_ = l_Lean_Expr_isApp(v___x_2558_);
                                if v___x_2559_ == 0 {
                                    lean_dec_ref(v___x_2558_);
                                    lean_dec_ref(v_arg_2557_);
                                    lean_dec_ref(v_arg_2554_);
                                    lean_dec_ref(v_e_2493_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2560_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2558_);
                                    v___x_2561_ = l_Lean_Expr_isApp(v___x_2560_);
                                    if v___x_2561_ == 0 {
                                        lean_dec_ref(v___x_2560_);
                                        lean_dec_ref(v_arg_2557_);
                                        lean_dec_ref(v_arg_2554_);
                                        lean_dec_ref(v_e_2493_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_2562_ = lean_ctor_get(v___x_2560_, 1);
                                        lean_inc_ref(v_arg_2562_);
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
                                                    lean_dec_ref(v___x_2563_);
                                                    if v___x_2571_ == 0 {
                                                        lean_dec_ref(v_arg_2562_);
                                                        lean_dec_ref(v_arg_2557_);
                                                        lean_dec_ref(v_arg_2554_);
                                                        lean_dec_ref(v_e_2493_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_2572_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2562_, v_a_2495_);
                                                        if lean_obj_tag(v___x_2572_) == 0 {
                                                            v_a_2573_ =
                                                                lean_ctor_get(v___x_2572_, 0);
                                                            lean_inc(v_a_2573_);
                                                            lean_dec_ref_known(v___x_2572_, 1);
                                                            v___x_2574_ =
                                                                l_Lean_Expr_cleanupAnnotations(
                                                                    v_a_2573_,
                                                                );
                                                            v___x_2575_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
                                                            v___x_2576_ = l_Lean_Expr_isConstOf(
                                                                v___x_2574_,
                                                                v___x_2575_,
                                                            );
                                                            lean_dec_ref(v___x_2574_);
                                                            if v___x_2576_ == 0 {
                                                                lean_dec_ref(v_arg_2557_);
                                                                lean_dec_ref(v_arg_2554_);
                                                                lean_dec_ref(v_e_2493_);
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_2577_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
                                                                lean_inc_ref(v_arg_2554_);
                                                                v___x_2578_ = l_Lean_mkIntAdd(
                                                                    v_arg_2554_,
                                                                    v___x_2577_,
                                                                );
                                                                lean_inc_ref(v_arg_2557_);
                                                                v___x_2579_ = l_Lean_mkIntLE(
                                                                    v___x_2578_,
                                                                    v_arg_2557_,
                                                                );
                                                                v___x_2580_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21);
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
                                                            lean_dec_ref(v_arg_2557_);
                                                            lean_dec_ref(v_arg_2554_);
                                                            lean_dec_ref(v_e_2493_);
                                                            v_a_2582_ =
                                                                lean_ctor_get(v___x_2572_, 0);
                                                            v_isSharedCheck_2589_ =
                                                                (!lean_is_exclusive(v___x_2572_))
                                                                    as u8;
                                                            if v_isSharedCheck_2589_ == 0 {
                                                                v___x_2584_ = v___x_2572_;
                                                                v_isShared_2585_ =
                                                                    v_isSharedCheck_2589_;
                                                                state = 10;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2582_);
                                                                lean_dec(v___x_2572_);
                                                                v___x_2584_ = lean_box(0);
                                                                v_isShared_2585_ =
                                                                    v_isSharedCheck_2589_;
                                                                state = 10;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_2563_);
                                                    v___x_2590_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2562_, v_a_2495_);
                                                    if lean_obj_tag(v___x_2590_) == 0 {
                                                        v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
                                                        lean_inc(v_a_2591_);
                                                        lean_dec_ref_known(v___x_2590_, 1);
                                                        v___x_2592_ =
                                                            l_Lean_Expr_cleanupAnnotations(
                                                                v_a_2591_,
                                                            );
                                                        v___x_2593_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
                                                        v___x_2594_ = l_Lean_Expr_isConstOf(
                                                            v___x_2592_,
                                                            v___x_2593_,
                                                        );
                                                        lean_dec_ref(v___x_2592_);
                                                        if v___x_2594_ == 0 {
                                                            lean_dec_ref(v_arg_2557_);
                                                            lean_dec_ref(v_arg_2554_);
                                                            lean_dec_ref(v_e_2493_);
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_2595_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
                                                            lean_inc_ref(v_arg_2557_);
                                                            v___x_2596_ = l_Lean_mkIntAdd(
                                                                v_arg_2557_,
                                                                v___x_2595_,
                                                            );
                                                            lean_inc_ref(v_arg_2554_);
                                                            v___x_2597_ = l_Lean_mkIntLE(
                                                                v___x_2596_,
                                                                v_arg_2554_,
                                                            );
                                                            v___x_2598_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24);
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
                                                        lean_dec_ref(v_arg_2557_);
                                                        lean_dec_ref(v_arg_2554_);
                                                        lean_dec_ref(v_e_2493_);
                                                        v_a_2600_ = lean_ctor_get(v___x_2590_, 0);
                                                        v_isSharedCheck_2607_ =
                                                            (!lean_is_exclusive(v___x_2590_)) as u8;
                                                        if v_isSharedCheck_2607_ == 0 {
                                                            v___x_2602_ = v___x_2590_;
                                                            v_isShared_2603_ =
                                                                v_isSharedCheck_2607_;
                                                            state = 12;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_2600_);
                                                            lean_dec(v___x_2590_);
                                                            v___x_2602_ = lean_box(0);
                                                            v_isShared_2603_ =
                                                                v_isSharedCheck_2607_;
                                                            state = 12;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_2563_);
                                                v___x_2608_ =
                                                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                        v_arg_2562_,
                                                        v_a_2495_,
                                                    );
                                                if lean_obj_tag(v___x_2608_) == 0 {
                                                    v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
                                                    lean_inc(v_a_2609_);
                                                    lean_dec_ref_known(v___x_2608_, 1);
                                                    v___x_2610_ =
                                                        l_Lean_Expr_cleanupAnnotations(v_a_2609_);
                                                    v___x_2611_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
                                                    v___x_2612_ = l_Lean_Expr_isConstOf(
                                                        v___x_2610_,
                                                        v___x_2611_,
                                                    );
                                                    lean_dec_ref(v___x_2610_);
                                                    if v___x_2612_ == 0 {
                                                        lean_dec_ref(v_arg_2557_);
                                                        lean_dec_ref(v_arg_2554_);
                                                        lean_dec_ref(v_e_2493_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        lean_inc_ref(v_arg_2557_);
                                                        lean_inc_ref(v_arg_2554_);
                                                        v___x_2613_ = l_Lean_mkIntLE(
                                                            v_arg_2554_,
                                                            v_arg_2557_,
                                                        );
                                                        v___x_2614_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27);
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
                                                    lean_dec_ref(v_arg_2557_);
                                                    lean_dec_ref(v_arg_2554_);
                                                    lean_dec_ref(v_e_2493_);
                                                    v_a_2616_ = lean_ctor_get(v___x_2608_, 0);
                                                    v_isSharedCheck_2623_ =
                                                        (!lean_is_exclusive(v___x_2608_)) as u8;
                                                    if v_isSharedCheck_2623_ == 0 {
                                                        v___x_2618_ = v___x_2608_;
                                                        v_isShared_2619_ = v_isSharedCheck_2623_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2616_);
                                                        lean_dec(v___x_2608_);
                                                        v___x_2618_ = lean_box(0);
                                                        v_isShared_2619_ = v_isSharedCheck_2623_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_2563_);
                                            v___x_2624_ =
                                                l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                    v_arg_2562_,
                                                    v_a_2495_,
                                                );
                                            if lean_obj_tag(v___x_2624_) == 0 {
                                                v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
                                                lean_inc(v_a_2625_);
                                                lean_dec_ref_known(v___x_2624_, 1);
                                                v___x_2626_ =
                                                    l_Lean_Expr_cleanupAnnotations(v_a_2625_);
                                                v___x_2627_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
                                                v___x_2628_ =
                                                    l_Lean_Expr_isConstOf(v___x_2626_, v___x_2627_);
                                                lean_dec_ref(v___x_2626_);
                                                if v___x_2628_ == 0 {
                                                    lean_dec_ref(v_arg_2557_);
                                                    lean_dec_ref(v_arg_2554_);
                                                    lean_dec_ref(v_e_2493_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_inc_ref(v_arg_2554_);
                                                    lean_inc_ref(v_arg_2557_);
                                                    v___x_2629_ =
                                                        l_Lean_mkIntLE(v_arg_2557_, v_arg_2554_);
                                                    v___x_2630_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once), _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30);
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
                                                lean_dec_ref(v_arg_2557_);
                                                lean_dec_ref(v_arg_2554_);
                                                lean_dec_ref(v_e_2493_);
                                                v_a_2632_ = lean_ctor_get(v___x_2624_, 0);
                                                v_isSharedCheck_2639_ =
                                                    (!lean_is_exclusive(v___x_2624_)) as u8;
                                                if v_isSharedCheck_2639_ == 0 {
                                                    v___x_2634_ = v___x_2624_;
                                                    v_isShared_2635_ = v_isSharedCheck_2639_;
                                                    state = 16;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2632_);
                                                    lean_dec(v___x_2624_);
                                                    v___x_2634_ = lean_box(0);
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
                        lean_dec_ref(v_e_2493_);
                        v_a_2640_ = lean_ctor_get(v___x_2550_, 0);
                        v_isSharedCheck_2647_ = (!lean_is_exclusive(v___x_2550_)) as u8;
                        if v_isSharedCheck_2647_ == 0 {
                            v___x_2642_ = v___x_2550_;
                            v_isShared_2643_ = v_isSharedCheck_2647_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_2640_);
                            lean_dec(v___x_2550_);
                            v___x_2642_ = lean_box(0);
                            v_isShared_2643_ = v_isSharedCheck_2647_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2500_ = lean_box(0);
                v___x_2501_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2501_, 0, v___x_2500_);
                return v___x_2501_;
            }
            2 => {
                v___x_2509_ = 0;
                lean_inc_ref(v_val_2503_);
                v___x_2510_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(
                    v_val_2503_,
                    v___x_2509_,
                    v___y_2505_,
                    v___y_2506_,
                    v___y_2507_,
                    v___y_2508_,
                );
                if lean_obj_tag(v___x_2510_) == 0 {
                    v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
                    v_isSharedCheck_2543_ = (!lean_is_exclusive(v___x_2510_)) as u8;
                    if v_isSharedCheck_2543_ == 0 {
                        v___x_2513_ = v___x_2510_;
                        v_isShared_2514_ = v_isSharedCheck_2543_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2511_);
                        lean_dec(v___x_2510_);
                        v___x_2513_ = lean_box(0);
                        v_isShared_2514_ = v_isSharedCheck_2543_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_h_u2081_2504_);
                    lean_dec_ref(v_val_2503_);
                    lean_dec_ref(v_e_2493_);
                    return v___x_2510_;
                }
            }
            3 => {
                if lean_obj_tag(v_a_2511_) == 1 {
                    v_val_2515_ = lean_ctor_get(v_a_2511_, 0);
                    v_isSharedCheck_2537_ = (!lean_is_exclusive(v_a_2511_)) as u8;
                    if v_isSharedCheck_2537_ == 0 {
                        v___x_2517_ = v_a_2511_;
                        v_isShared_2518_ = v_isSharedCheck_2537_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_2515_);
                        lean_dec(v_a_2511_);
                        v___x_2517_ = lean_box(0);
                        v_isShared_2518_ = v_isSharedCheck_2537_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2511_);
                    lean_dec_ref(v_e_2493_);
                    v___x_2538_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2538_, 0, v_val_2503_);
                    lean_ctor_set(v___x_2538_, 1, v_h_u2081_2504_);
                    v___x_2539_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2539_, 0, v___x_2538_);
                    if v_isShared_2514_ == 0 {
                        lean_ctor_set(v___x_2513_, 0, v___x_2539_);
                        v___x_2541_ = v___x_2513_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
                        v___x_2541_ = v_reuseFailAlloc_2542_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2519_ = lean_ctor_get(v_val_2515_, 0);
                v_snd_2520_ = lean_ctor_get(v_val_2515_, 1);
                v_isSharedCheck_2536_ = (!lean_is_exclusive(v_val_2515_)) as u8;
                if v_isSharedCheck_2536_ == 0 {
                    v___x_2522_ = v_val_2515_;
                    v_isShared_2523_ = v_isSharedCheck_2536_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_2520_);
                    lean_inc(v_fst_2519_);
                    lean_dec(v_val_2515_);
                    v___x_2522_ = lean_box(0);
                    v_isShared_2523_ = v_isSharedCheck_2536_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2524_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5,
                );
                v___x_2525_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6,
                );
                lean_inc(v_fst_2519_);
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
                    lean_ctor_set(v___x_2522_, 1, v___x_2526_);
                    v___x_2528_ = v___x_2522_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_fst_2519_);
                    lean_ctor_set(v_reuseFailAlloc_2535_, 1, v___x_2526_);
                    v___x_2528_ = v_reuseFailAlloc_2535_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2518_ == 0 {
                    lean_ctor_set(v___x_2517_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2517_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2528_);
                    v___x_2530_ = v_reuseFailAlloc_2534_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2514_ == 0 {
                    lean_ctor_set(v___x_2513_, 0, v___x_2530_);
                    v___x_2532_ = v___x_2513_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
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
                    v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
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
                    v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
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
                    v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
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
                    v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
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
                    v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
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
    mut v_e_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
    mut v_a_2651_: *mut LeanObject,
    mut v_a_2652_: *mut LeanObject,
    mut v_a_2653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2654_: *mut LeanObject = core::ptr::null_mut();
    v_res_2654_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(
        v_e_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_,
    );
    lean_dec(v_a_2652_);
    lean_dec_ref(v_a_2651_);
    lean_dec(v_a_2650_);
    lean_dec_ref(v_a_2649_);
    return v_res_2654_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(
    mut v_snd_2655_: *mut LeanObject,
    mut v_x_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    v___x_2657_ = l_Lean_instInhabitedExpr;
    v___x_2658_ = lean_array_get_borrowed(v___x_2657_, v_snd_2655_, v_x_2656_);
    lean_inc(v___x_2658_);
    return v___x_2658_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed(
    mut v_snd_2659_: *mut LeanObject,
    mut v_x_2660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2661_: *mut LeanObject = core::ptr::null_mut();
    v_res_2661_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(v_snd_2659_, v_x_2660_);
    lean_dec(v_x_2660_);
    lean_dec_ref(v_snd_2659_);
    return v_res_2661_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    v___x_2667_ = lean_box(0);
    v___x_2668_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1;
    v___x_2669_ = l_Lean_mkConst(v___x_2668_, v___x_2667_);
    return v___x_2669_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5() -> *mut LeanObject {
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    v___x_2675_ = lean_box(0);
    v___x_2676_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4;
    v___x_2677_ = l_Lean_mkConst(v___x_2676_, v___x_2675_);
    return v___x_2677_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8() -> *mut LeanObject {
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    v___x_2683_ = lean_box(0);
    v___x_2684_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7;
    v___x_2685_ = l_Lean_mkConst(v___x_2684_, v___x_2683_);
    return v___x_2685_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(
    mut v_e_2686_: *mut LeanObject,
    mut v_a_2687_: *mut LeanObject,
    mut v_a_2688_: *mut LeanObject,
    mut v_a_2689_: *mut LeanObject,
    mut v_a_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2717_: u8 = 0;
    let mut v_val_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2721_: u8 = 0;
    let mut v_snd_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2773_: u8 = 0;
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2777_: u8 = 0;
    let mut v___x_2778_: u8 = 0;
    let mut v___f_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___y_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: u8 = 0;
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2797_: u8 = 0;
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_a_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: u8 = 0;
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2842_: u8 = 0;
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v_a_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2874_: u8 = 0;
    let mut v_isSharedCheck_2875_: u8 = 0;
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut v_a_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2713_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(
                    v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_,
                );
                if lean_obj_tag(v___x_2713_) == 0 {
                    v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
                    v_isSharedCheck_2880_ = (!lean_is_exclusive(v___x_2713_)) as u8;
                    if v_isSharedCheck_2880_ == 0 {
                        v___x_2716_ = v___x_2713_;
                        v_isShared_2717_ = v_isSharedCheck_2880_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2714_);
                        lean_dec(v___x_2713_);
                        v___x_2716_ = lean_box(0);
                        v_isShared_2717_ = v_isSharedCheck_2880_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2881_ = lean_ctor_get(v___x_2713_, 0);
                    v_isSharedCheck_2888_ = (!lean_is_exclusive(v___x_2713_)) as u8;
                    if v_isSharedCheck_2888_ == 0 {
                        v___x_2883_ = v___x_2713_;
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 26;
                        continue;
                    } else {
                        lean_inc(v_a_2881_);
                        lean_dec(v___x_2713_);
                        v___x_2883_ = lean_box(0);
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 26;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_2694_);
                v___x_2696_ = l_Lean_mkPropEq(v___y_2693_, v___y_2694_);
                v___x_2697_ = l_Lean_Meta_mkExpectedPropHint(v_h_2695_, v___x_2696_);
                v___x_2698_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2698_, 0, v___y_2694_);
                lean_ctor_set(v___x_2698_, 1, v___x_2697_);
                v___x_2699_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2699_, 0, v___x_2698_);
                v___x_2700_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2700_, 0, v___x_2699_);
                return v___x_2700_;
            }
            2 => {
                v___x_2711_ = l_Lean_eagerReflBoolTrue;
                lean_inc_ref(v___y_2703_);
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
                if lean_obj_tag(v_a_2714_) == 1 {
                    v_val_2718_ = lean_ctor_get(v_a_2714_, 0);
                    v_isSharedCheck_2875_ = (!lean_is_exclusive(v_a_2714_)) as u8;
                    if v_isSharedCheck_2875_ == 0 {
                        v___x_2720_ = v_a_2714_;
                        v_isShared_2721_ = v_isSharedCheck_2875_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_2718_);
                        lean_dec(v_a_2714_);
                        v___x_2720_ = lean_box(0);
                        v_isShared_2721_ = v_isSharedCheck_2875_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2714_);
                    v___x_2876_ = lean_box(0);
                    if v_isShared_2717_ == 0 {
                        lean_ctor_set(v___x_2716_, 0, v___x_2876_);
                        v___x_2878_ = v___x_2716_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
                        v___x_2878_ = v_reuseFailAlloc_2879_;
                        state = 25;
                        continue;
                    }
                }
            }
            4 => {
                v_snd_2722_ = lean_ctor_get(v_val_2718_, 1);
                lean_inc(v_snd_2722_);
                v_fst_2723_ = lean_ctor_get(v_val_2718_, 0);
                lean_inc(v_fst_2723_);
                lean_dec(v_val_2718_);
                v_fst_2724_ = lean_ctor_get(v_snd_2722_, 0);
                v_snd_2725_ = lean_ctor_get(v_snd_2722_, 1);
                v_isSharedCheck_2874_ = (!lean_is_exclusive(v_snd_2722_)) as u8;
                if v_isSharedCheck_2874_ == 0 {
                    v___x_2727_ = v_snd_2722_;
                    v_isShared_2728_ = v_isSharedCheck_2874_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_2725_);
                    lean_inc(v_fst_2724_);
                    lean_dec(v_snd_2722_);
                    v___x_2727_ = lean_box(0);
                    v_isShared_2728_ = v_isSharedCheck_2874_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2729_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5,
                );
                v___x_2778_ = lean_int_dec_eq(v_fst_2723_, v___x_2729_);
                if v___x_2778_ == 0 {
                    lean_del_object(v___x_2716_);
                    lean_inc(v_snd_2725_);
                    v___f_2779_ = lean_alloc_closure(
                        l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2779_, 0, v_snd_2725_);
                    lean_inc(v_fst_2724_);
                    lean_inc_ref(v___f_2779_);
                    v___x_2780_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_2779_, v_fst_2724_);
                    if lean_obj_tag(v___x_2780_) == 0 {
                        v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
                        v_isSharedCheck_2861_ = (!lean_is_exclusive(v___x_2780_)) as u8;
                        if v_isSharedCheck_2861_ == 0 {
                            v___x_2783_ = v___x_2780_;
                            v_isShared_2784_ = v_isSharedCheck_2861_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_2781_);
                            lean_dec(v___x_2780_);
                            v___x_2783_ = lean_box(0);
                            v_isShared_2784_ = v_isSharedCheck_2861_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___f_2779_);
                        lean_del_object(v___x_2727_);
                        lean_dec(v_snd_2725_);
                        lean_dec(v_fst_2724_);
                        lean_dec(v_fst_2723_);
                        lean_del_object(v___x_2720_);
                        v_a_2862_ = lean_ctor_get(v___x_2780_, 0);
                        v_isSharedCheck_2869_ = (!lean_is_exclusive(v___x_2780_)) as u8;
                        if v_isSharedCheck_2869_ == 0 {
                            v___x_2864_ = v___x_2780_;
                            v_isShared_2865_ = v_isSharedCheck_2869_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_2862_);
                            lean_dec(v___x_2780_);
                            v___x_2864_ = lean_box(0);
                            v_isShared_2865_ = v_isSharedCheck_2869_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2727_);
                    lean_dec(v_snd_2725_);
                    lean_dec(v_fst_2724_);
                    lean_dec(v_fst_2723_);
                    lean_del_object(v___x_2720_);
                    v___x_2870_ = lean_box(0);
                    if v_isShared_2717_ == 0 {
                        lean_ctor_set(v___x_2716_, 0, v___x_2870_);
                        v___x_2872_ = v___x_2716_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
                        v___x_2872_ = v_reuseFailAlloc_2873_;
                        state = 24;
                        continue;
                    }
                }
            }
            6 => {
                lean_inc_ref(v___y_2736_);
                v___x_2737_ = l_Lean_mkIntDvd(v___y_2736_, v___y_2733_);
                v___x_2738_ = lean_obj_once(
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
                    if lean_obj_tag(v___x_2740_) == 0 {
                        v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
                        lean_inc(v_a_2741_);
                        lean_dec_ref_known(v___x_2740_, 1);
                        v___x_2742_ = lean_obj_once(
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
                            v___x_2746_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                            );
                            v___x_2747_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                            );
                            v___x_2748_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                ),
                                _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                            );
                            v___x_2749_ = lean_int_neg(v___y_2734_);
                            lean_dec(v___y_2734_);
                            v___x_2750_ = l_Int_toNat(v___x_2749_);
                            lean_dec(v___x_2749_);
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
                            lean_dec(v___y_2734_);
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
                        lean_dec_ref(v___x_2737_);
                        lean_dec_ref(v___y_2736_);
                        lean_dec_ref(v___y_2735_);
                        lean_dec(v___y_2734_);
                        lean_dec_ref(v___y_2732_);
                        lean_dec_ref(v___y_2731_);
                        lean_dec(v_fst_2724_);
                        v_a_2755_ = lean_ctor_get(v___x_2740_, 0);
                        v_isSharedCheck_2762_ = (!lean_is_exclusive(v___x_2740_)) as u8;
                        if v_isSharedCheck_2762_ == 0 {
                            v___x_2757_ = v___x_2740_;
                            v_isShared_2758_ = v_isSharedCheck_2762_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2755_);
                            lean_dec(v___x_2740_);
                            v___x_2757_ = lean_box(0);
                            v_isShared_2758_ = v_isSharedCheck_2762_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_2736_);
                    lean_dec(v___y_2734_);
                    v___x_2763_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_2725_,
                        v_a_2687_,
                        v_a_2688_,
                        v_a_2689_,
                        v_a_2690_,
                    );
                    if lean_obj_tag(v___x_2763_) == 0 {
                        v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
                        lean_inc(v_a_2764_);
                        lean_dec_ref_known(v___x_2763_, 1);
                        v___x_2765_ = lean_obj_once(
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
                        lean_dec_ref(v___x_2737_);
                        lean_dec_ref(v___y_2735_);
                        lean_dec_ref(v___y_2732_);
                        lean_dec_ref(v___y_2731_);
                        lean_dec(v_fst_2724_);
                        v_a_2770_ = lean_ctor_get(v___x_2763_, 0);
                        v_isSharedCheck_2777_ = (!lean_is_exclusive(v___x_2763_)) as u8;
                        if v_isSharedCheck_2777_ == 0 {
                            v___x_2772_ = v___x_2763_;
                            v_isShared_2773_ = v_isSharedCheck_2777_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2770_);
                            lean_dec(v___x_2763_);
                            v___x_2772_ = lean_box(0);
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
                    v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
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
                    v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
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
                    v___x_2852_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                    );
                    v___x_2853_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                    );
                    v___x_2854_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                    );
                    v___x_2855_ = lean_int_neg(v_fst_2723_);
                    v___x_2856_ = l_Int_toNat(v___x_2855_);
                    lean_dec(v___x_2855_);
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
                lean_inc_ref(v___y_2786_);
                v___x_2787_ = l_Lean_mkIntDvd(v___y_2786_, v_a_2781_);
                v___x_2788_ = l_Int_Linear_Expr_norm(v_fst_2724_);
                lean_inc(v_fst_2723_);
                v___x_2789_ = l_Int_Linear_Poly_gcdCoeffs(v___x_2788_, v_fst_2723_);
                v___x_2790_ = l_Int_Linear_Poly_getConst(v___x_2788_);
                v___x_2791_ = lean_int_emod(v___x_2790_, v___x_2789_);
                lean_dec(v___x_2790_);
                v___x_2792_ = lean_int_dec_eq(v___x_2791_, v___x_2729_);
                lean_dec(v___x_2791_);
                if v___x_2792_ == 0 {
                    lean_dec(v___x_2789_);
                    lean_dec_ref(v___x_2788_);
                    lean_del_object(v___x_2783_);
                    lean_dec_ref(v___f_2779_);
                    lean_dec(v_fst_2723_);
                    v___x_2793_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_2725_,
                        v_a_2687_,
                        v_a_2688_,
                        v_a_2689_,
                        v_a_2690_,
                    );
                    if lean_obj_tag(v___x_2793_) == 0 {
                        v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
                        v_isSharedCheck_2814_ = (!lean_is_exclusive(v___x_2793_)) as u8;
                        if v_isSharedCheck_2814_ == 0 {
                            v___x_2796_ = v___x_2793_;
                            v_isShared_2797_ = v_isSharedCheck_2814_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_2794_);
                            lean_dec(v___x_2793_);
                            v___x_2796_ = lean_box(0);
                            v_isShared_2797_ = v_isSharedCheck_2814_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_2787_);
                        lean_dec_ref(v___y_2786_);
                        lean_del_object(v___x_2727_);
                        lean_dec(v_fst_2724_);
                        lean_del_object(v___x_2720_);
                        v_a_2815_ = lean_ctor_get(v___x_2793_, 0);
                        v_isSharedCheck_2822_ = (!lean_is_exclusive(v___x_2793_)) as u8;
                        if v_isSharedCheck_2822_ == 0 {
                            v___x_2817_ = v___x_2793_;
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_2815_);
                            lean_dec(v___x_2793_);
                            v___x_2817_ = lean_box(0);
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2727_);
                    lean_del_object(v___x_2720_);
                    v___x_2823_ = l_Int_Linear_Poly_div(v___x_2789_, v___x_2788_);
                    lean_inc_ref(v___x_2823_);
                    v___x_2824_ = l_Int_Linear_Poly_toExpr(v___x_2823_);
                    v___x_2825_ = l_Int_Linear_instBEqExpr_beq(v_fst_2724_, v___x_2824_);
                    lean_dec_ref(v___x_2824_);
                    if v___x_2825_ == 0 {
                        lean_del_object(v___x_2783_);
                        lean_inc_ref(v___x_2823_);
                        v___x_2826_ =
                            l_Int_Linear_Poly_denoteExpr___redArg(v___f_2779_, v___x_2823_);
                        if lean_obj_tag(v___x_2826_) == 0 {
                            v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
                            lean_inc(v_a_2827_);
                            lean_dec_ref_known(v___x_2826_, 1);
                            v___x_2828_ = lean_int_ediv(v_fst_2723_, v___x_2789_);
                            lean_dec(v_fst_2723_);
                            v___x_2829_ = lean_int_dec_le(v___x_2729_, v___x_2828_);
                            if v___x_2829_ == 0 {
                                v___x_2830_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17,
                                );
                                v___x_2831_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19,
                                );
                                v___x_2832_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once
                                    ),
                                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22,
                                );
                                v___x_2833_ = lean_int_neg(v___x_2828_);
                                lean_dec(v___x_2828_);
                                v___x_2834_ = l_Int_toNat(v___x_2833_);
                                lean_dec(v___x_2833_);
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
                                lean_dec(v___x_2828_);
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
                            lean_dec_ref(v___x_2823_);
                            lean_dec(v___x_2789_);
                            lean_dec_ref(v___x_2787_);
                            lean_dec_ref(v___y_2786_);
                            lean_dec(v_snd_2725_);
                            lean_dec(v_fst_2724_);
                            lean_dec(v_fst_2723_);
                            v_a_2839_ = lean_ctor_get(v___x_2826_, 0);
                            v_isSharedCheck_2846_ = (!lean_is_exclusive(v___x_2826_)) as u8;
                            if v_isSharedCheck_2846_ == 0 {
                                v___x_2841_ = v___x_2826_;
                                v_isShared_2842_ = v_isSharedCheck_2846_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_2839_);
                                lean_dec(v___x_2826_);
                                v___x_2841_ = lean_box(0);
                                v_isShared_2842_ = v_isSharedCheck_2846_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2823_);
                        lean_dec(v___x_2789_);
                        lean_dec_ref(v___x_2787_);
                        lean_dec_ref(v___y_2786_);
                        lean_dec_ref(v___f_2779_);
                        lean_dec(v_snd_2725_);
                        lean_dec(v_fst_2724_);
                        lean_dec(v_fst_2723_);
                        v___x_2847_ = lean_box(0);
                        if v_isShared_2784_ == 0 {
                            lean_ctor_set(v___x_2783_, 0, v___x_2847_);
                            v___x_2849_ = v___x_2783_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
                            v___x_2849_ = v_reuseFailAlloc_2850_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            13 => {
                v___x_2798_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once),
                    _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8,
                );
                v___x_2799_ = lean_obj_once(
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
                    lean_ctor_set(v___x_2727_, 1, v___x_2804_);
                    lean_ctor_set(v___x_2727_, 0, v___x_2798_);
                    v___x_2806_ = v___x_2727_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2798_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___x_2804_);
                    v___x_2806_ = v_reuseFailAlloc_2813_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2721_ == 0 {
                    lean_ctor_set(v___x_2720_, 0, v___x_2806_);
                    v___x_2808_ = v___x_2720_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2806_);
                    v___x_2808_ = v_reuseFailAlloc_2812_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2797_ == 0 {
                    lean_ctor_set(v___x_2796_, 0, v___x_2808_);
                    v___x_2810_ = v___x_2796_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
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
                    v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
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
                    v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
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
                    v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
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
                    v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
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
    mut v_e_2889_: *mut LeanObject,
    mut v_a_2890_: *mut LeanObject,
    mut v_a_2891_: *mut LeanObject,
    mut v_a_2892_: *mut LeanObject,
    mut v_a_2893_: *mut LeanObject,
    mut v_a_2894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2895_: *mut LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(
        v_e_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_,
    );
    lean_dec(v_a_2893_);
    lean_dec_ref(v_a_2892_);
    lean_dec(v_a_2891_);
    lean_dec_ref(v_a_2890_);
    return v_res_2895_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    v___x_2903_ = lean_box(0);
    v___x_2904_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2;
    v___x_2905_ = l_Lean_mkConst(v___x_2904_, v___x_2903_);
    return v___x_2905_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(
    mut v_lhs_2906_: *mut LeanObject,
    mut v_a_2907_: *mut LeanObject,
    mut v_a_2908_: *mut LeanObject,
    mut v_a_2909_: *mut LeanObject,
    mut v_a_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v_fst_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2921_: u8 = 0;
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2949_: u8 = 0;
    let mut v_a_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2953_: u8 = 0;
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2957_: u8 = 0;
    let mut v_a_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut v_a_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2973_: u8 = 0;
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut v_isSharedCheck_2979_: u8 = 0;
    let mut v_a_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2912_) == 0 {
                    v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
                    v_isSharedCheck_2979_ = (!lean_is_exclusive(v___x_2912_)) as u8;
                    if v_isSharedCheck_2979_ == 0 {
                        v___x_2915_ = v___x_2912_;
                        v_isShared_2916_ = v_isSharedCheck_2979_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2913_);
                        lean_dec(v___x_2912_);
                        v___x_2915_ = lean_box(0);
                        v_isShared_2916_ = v_isSharedCheck_2979_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2980_ = lean_ctor_get(v___x_2912_, 0);
                    v_isSharedCheck_2987_ = (!lean_is_exclusive(v___x_2912_)) as u8;
                    if v_isSharedCheck_2987_ == 0 {
                        v___x_2982_ = v___x_2912_;
                        v_isShared_2983_ = v_isSharedCheck_2987_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_2980_);
                        lean_dec(v___x_2912_);
                        v___x_2982_ = lean_box(0);
                        v_isShared_2983_ = v_isSharedCheck_2987_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2917_ = lean_ctor_get(v_a_2913_, 0);
                v_snd_2918_ = lean_ctor_get(v_a_2913_, 1);
                v_isSharedCheck_2978_ = (!lean_is_exclusive(v_a_2913_)) as u8;
                if v_isSharedCheck_2978_ == 0 {
                    v___x_2920_ = v_a_2913_;
                    v_isShared_2921_ = v_isSharedCheck_2978_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2918_);
                    lean_inc(v_fst_2917_);
                    lean_dec(v_a_2913_);
                    v___x_2920_ = lean_box(0);
                    v_isShared_2921_ = v_isSharedCheck_2978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2922_ = l_Int_Linear_Expr_norm(v_fst_2917_);
                lean_inc_ref(v___x_2922_);
                v___x_2923_ = l_Int_Linear_Poly_toExpr(v___x_2922_);
                v___x_2924_ = l_Int_Linear_instBEqExpr_beq(v_fst_2917_, v___x_2923_);
                lean_dec_ref(v___x_2923_);
                if v___x_2924_ == 0 {
                    lean_del_object(v___x_2915_);
                    lean_inc(v_snd_2918_);
                    v___x_2925_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(
                        v_snd_2918_,
                        v_a_2907_,
                        v_a_2908_,
                        v_a_2909_,
                        v_a_2910_,
                    );
                    if lean_obj_tag(v___x_2925_) == 0 {
                        v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
                        lean_inc(v_a_2926_);
                        lean_dec_ref_known(v___x_2925_, 1);
                        v___f_2927_ = lean_alloc_closure(
                            l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        lean_closure_set(v___f_2927_, 0, v_snd_2918_);
                        lean_inc(v_fst_2917_);
                        v___x_2928_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_2917_);
                        lean_inc_ref(v___f_2927_);
                        v___x_2929_ =
                            l_Int_Linear_Expr_denoteExpr___redArg(v___f_2927_, v_fst_2917_);
                        if lean_obj_tag(v___x_2929_) == 0 {
                            v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
                            lean_inc(v_a_2930_);
                            lean_dec_ref_known(v___x_2929_, 1);
                            lean_inc_ref(v___x_2922_);
                            v___x_2931_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_2922_);
                            v___x_2932_ =
                                l_Int_Linear_Poly_denoteExpr___redArg(v___f_2927_, v___x_2922_);
                            if lean_obj_tag(v___x_2932_) == 0 {
                                v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
                                v_isSharedCheck_2949_ = (!lean_is_exclusive(v___x_2932_)) as u8;
                                if v_isSharedCheck_2949_ == 0 {
                                    v___x_2935_ = v___x_2932_;
                                    v_isShared_2936_ = v_isSharedCheck_2949_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2933_);
                                    lean_dec(v___x_2932_);
                                    v___x_2935_ = lean_box(0);
                                    v_isShared_2936_ = v_isSharedCheck_2949_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_2931_);
                                lean_dec(v_a_2930_);
                                lean_dec_ref(v___x_2928_);
                                lean_dec(v_a_2926_);
                                lean_del_object(v___x_2920_);
                                v_a_2950_ = lean_ctor_get(v___x_2932_, 0);
                                v_isSharedCheck_2957_ = (!lean_is_exclusive(v___x_2932_)) as u8;
                                if v_isSharedCheck_2957_ == 0 {
                                    v___x_2952_ = v___x_2932_;
                                    v_isShared_2953_ = v_isSharedCheck_2957_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_2950_);
                                    lean_dec(v___x_2932_);
                                    v___x_2952_ = lean_box(0);
                                    v_isShared_2953_ = v_isSharedCheck_2957_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_2928_);
                            lean_dec_ref(v___f_2927_);
                            lean_dec(v_a_2926_);
                            lean_dec_ref(v___x_2922_);
                            lean_del_object(v___x_2920_);
                            v_a_2958_ = lean_ctor_get(v___x_2929_, 0);
                            v_isSharedCheck_2965_ = (!lean_is_exclusive(v___x_2929_)) as u8;
                            if v_isSharedCheck_2965_ == 0 {
                                v___x_2960_ = v___x_2929_;
                                v_isShared_2961_ = v_isSharedCheck_2965_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2958_);
                                lean_dec(v___x_2929_);
                                v___x_2960_ = lean_box(0);
                                v_isShared_2961_ = v_isSharedCheck_2965_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2922_);
                        lean_del_object(v___x_2920_);
                        lean_dec(v_snd_2918_);
                        lean_dec(v_fst_2917_);
                        v_a_2966_ = lean_ctor_get(v___x_2925_, 0);
                        v_isSharedCheck_2973_ = (!lean_is_exclusive(v___x_2925_)) as u8;
                        if v_isSharedCheck_2973_ == 0 {
                            v___x_2968_ = v___x_2925_;
                            v_isShared_2969_ = v_isSharedCheck_2973_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2966_);
                            lean_dec(v___x_2925_);
                            v___x_2968_ = lean_box(0);
                            v_isShared_2969_ = v_isSharedCheck_2973_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2922_);
                    lean_del_object(v___x_2920_);
                    lean_dec(v_snd_2918_);
                    lean_dec(v_fst_2917_);
                    v___x_2974_ = lean_box(0);
                    if v_isShared_2916_ == 0 {
                        lean_ctor_set(v___x_2915_, 0, v___x_2974_);
                        v___x_2976_ = v___x_2915_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
                        v___x_2976_ = v_reuseFailAlloc_2977_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2937_ = lean_obj_once(
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
                lean_inc(v_a_2933_);
                v___x_2940_ = l_Lean_mkIntEq(v_a_2930_, v_a_2933_);
                v___x_2941_ = l_Lean_Meta_mkExpectedPropHint(v___x_2939_, v___x_2940_);
                if v_isShared_2921_ == 0 {
                    lean_ctor_set(v___x_2920_, 1, v___x_2941_);
                    lean_ctor_set(v___x_2920_, 0, v_a_2933_);
                    v___x_2943_ = v___x_2920_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2933_);
                    lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2941_);
                    v___x_2943_ = v_reuseFailAlloc_2948_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2944_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2944_, 0, v___x_2943_);
                if v_isShared_2936_ == 0 {
                    lean_ctor_set(v___x_2935_, 0, v___x_2944_);
                    v___x_2946_ = v___x_2935_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
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
                    v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
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
                    v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
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
                    v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
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
                    v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
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
    mut v_lhs_2988_: *mut LeanObject,
    mut v_a_2989_: *mut LeanObject,
    mut v_a_2990_: *mut LeanObject,
    mut v_a_2991_: *mut LeanObject,
    mut v_a_2992_: *mut LeanObject,
    mut v_a_2993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2994_: *mut LeanObject = core::ptr::null_mut();
    v_res_2994_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(
        v_lhs_2988_,
        v_a_2989_,
        v_a_2990_,
        v_a_2991_,
        v_a_2992_,
    );
    lean_dec(v_a_2992_);
    lean_dec_ref(v_a_2991_);
    lean_dec(v_a_2990_);
    lean_dec_ref(v_a_2989_);
    return v_res_2994_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
}
